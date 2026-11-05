import json
import math
import mimetypes
import os
import re
from fractions import Fraction
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT_DIR = Path(__file__).parent
STATIC_DIR = ROOT_DIR / "static"
FORMALIZATION_DIR = ROOT_DIR / "Formalization"


def cfac_scalar(D: float) -> float:
    if D <= 1e-15:
        return 0.0
    return (D ** 2) * math.log(2.0 * D) - 1.5 * (D ** 2)


def int_h_func(u: float) -> float:
    if u <= 0.0:
        return 0.0
    if u >= 1.0:
        return 2.0 * math.log(2.0) - 1.0
    return (
        0.5
        * (
            (1.0 + u) ** 2 * math.log(1.0 + u)
            - (1.0 - u) ** 2 * math.log(1.0 - u)
        )
        - u
    )


def compute_closed_form_bounds(n_val: int, A0_override: float | None = None) -> dict:
    dL = 2 * n_val - 1
    if A0_override is not None:
        A0 = A0_override
        c0 = dL * A0
        A = 2.5 * c0
    else:
        c0 = 0.03
        A = 0.075
        A0 = c0 / dL
    C = A0
    Rc = 2.0 * (n_val - 1) * A0
    Rc_each = 2.0 * A0 if n_val >= 2 else 0.0
    Cfac = -(
        cfac_scalar(C)
        + max(n_val - 1, 1) * cfac_scalar(Rc_each)
        + cfac_scalar(C + Rc)
    )
    G0 = 2.0 * c0 * (math.log(2.0 * A0) - 1.0) - dL * (
        (A + A0) * (math.log(A + A0) - 1.0)
        - (A - A0) * (math.log(A - A0) - 1.0)
    )
    cont_base = (C ** 2) * (math.log(C / 4.0) - 1.5 + math.log(2.0 * A)) + C * G0
    kpc_std = 2.0 * C * Rc * math.log(A)
    if n_val >= 2:
        u_rc = Rc / A
        kpc_tight = C * Rc * (
            2.0 * math.log(A)
            + (1.0 + u_rc) * math.log(1.0 + u_rc)
            + (1.0 - u_rc) * math.log(1.0 - u_rc)
            - 2.0
        )
        kpp_exact = 2.0 * math.log(A0) + 2.0 * math.log(2.0) - 3.0
        wp_exact = (
            4.0 * A * math.log(2.0)
            - (2.0 * (A ** 2) / A0) * int_h_func(A0 / A)
            + c0
        )
        pole_jmax = (
            2.0 * n_val * (n_val - 1) * (A0 ** 2) * kpp_exact + Rc * wp_exact
        )
    else:
        kpc_tight = 0.0
        pole_jmax = 0.0
    ub_std = cont_base + kpc_std + pole_jmax + Cfac
    ub_tight = cont_base + kpc_tight + pole_jmax + Cfac

    len_I1 = max(0.0, A - 2.0 * A0)
    len_I2 = (
        max(0.0, (2.0 * A / 3.0) - max(2.0 * A0, 0.5 * (A + A0)))
        if A >= 3.0 * A0
        else 0.0
    )
    len_I3 = (
        max(0.0, (2.0 * A / 5.0) - max(2.0 * A0, (A + A0) / 3.0))
        if A >= 3.0 * A0
        else 0.0
    )
    tot_pos_len = len_I1 + len_I2 + len_I3
    rem_len = (2.0 * A - 2.0 * A0) - tot_pos_len
    bar_m1 = min(float(n_val - 1), 2.0) if n_val >= 2 else 0.0
    quad_m1_gain = (2.0 * A - 2.0 * A0) * (2.0 * A0 * bar_m1 * (bar_m1 - 1.0))
    I_occ_lb = (
        tot_pos_len * (2.0 * C + 2.0 * min(Rc, 4.0 * A0))
        + quad_m1_gain
        - 2.0 * C * rem_len
        - (c0 ** 2) * (1.5 + 4.0 / (dL ** 2))
    )
    phi_ub = -Cfac - I_occ_lb
    return {
        "n": n_val,
        "L_in": dL + 2,
        "A0": A0,
        "Rc": Rc,
        "A": A,
        "C_fac": Cfac,
        "Lambda_arch_UB": ub_std,
        "Lambda_arch_tight": ub_tight,
        "Phi_den_UB": phi_ub,
        "Net_UB_std": ub_std + phi_ub,
        "Net_UB_tight": ub_tight + phi_ub,
        "strictly_negative": (ub_std + phi_ub) < 0 and (ub_tight + phi_ub) < 0,
    }


def scan_lean_files() -> list[dict]:
    files_info = []
    lean_paths = sorted(FORMALIZATION_DIR.glob("*.lean")) if FORMALIZATION_DIR.exists() else []
    root_lean = ROOT_DIR / "Formalization.lean"
    if root_lean.exists():
        lean_paths = [root_lean] + lean_paths

    decl_pattern = re.compile(
        r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*(theorem|lemma|def|abbrev|axiom|structure)\s+([A-Za-z0-9_']+)",
        re.MULTILINE,
    )
    for p in lean_paths:
        content = p.read_text(encoding="utf-8")
        decls = [{"kind": m.group(1), "name": m.group(2)} for m in decl_pattern.finditer(content)]
        code_no_comments = re.sub(r"/-.*?-/", "", content, flags=re.DOTALL)
        code_no_comments = re.sub(r"--.*$", "", code_no_comments, flags=re.MULTILINE)
        sorry_count = len(re.findall(r"\b(sorry|admit)\b", code_no_comments))
        files_info.append(
            {
                "path": str(p.relative_to(ROOT_DIR)),
                "lines": len(content.splitlines()),
                "declarations": decls,
                "declaration_count": len(decls),
                "sorry_count": sorry_count,
                "content": content,
            }
        )
    return files_info


def compute_central_factorial_payload(m: int, r: int) -> dict:
    c1 = math.comb(r + m, 2 * m)
    c2 = math.comb(r + m - 1, 2 * m) if (r + m - 1) >= 0 else 0
    val_binom = Fraction(c1 + c2, 2)
    prod = Fraction(1, 1)
    for j in range(1, m + 1):
        prod *= Fraction(r * r - j * j, 1)
    val_poly = prod / Fraction(math.factorial(2 * m), 1)
    result = {
        "m": m,
        "r": r,
        "E_m_r2_poly": str(val_poly),
        "E_m_r2_binom": str(val_binom),
        "identically_equal": val_poly == val_binom,
        "in_root_window": 1 <= r <= m,
    }
    if 1 <= r <= m:
        sign = -1 if ((m - r) % 2 == 1) else 1
        den = math.factorial(m - r) * math.factorial(m + r)
        e_prime = Fraction(sign * r, den)
        recip = Fraction(1, 1) / e_prime
        t_mr = sum(
            Fraction(1, r * r - j * j) for j in range(1, m + 1) if j != r
        )
        e_second_half = e_prime * t_mr
        result.update(
            {
                "E_prime_r2": f"{e_prime.numerator}/{e_prime.denominator}",
                "reciprocal_E_prime": str(recip.numerator),
                "reciprocal_is_nonzero_int": recip.denominator == 1 and recip.numerator != 0,
                "T_m_r": f"{t_mr.numerator}/{t_mr.denominator}",
                "half_E_double_prime_r2": f"{e_second_half.numerator}/{e_second_half.denominator}",
            }
        )
    return result


class AppRequestHandler(BaseHTTPRequestHandler):
    def log_message(self, format: str, *args) -> None:
        return

    def _send_json(self, payload: dict, status: int = 200) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_file(self, file_path: Path) -> None:
        if not file_path.exists() or not file_path.is_file():
            self.send_error(404, "Not Found")
            return
        content_type, _ = mimetypes.guess_type(str(file_path))
        if not content_type:
            content_type = "application/octet-stream"
        data = file_path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        qs = parse_qs(parsed.query)

        if path == "/api/health":
            self._send_json({"status": "ok"})
            return

        if path == "/api/status":
            files = scan_lean_files()
            total_decls = sum(f["declaration_count"] for f in files)
            total_sorries = sum(f["sorry_count"] for f in files)
            table4 = [
                compute_closed_form_bounds(n)
                for n in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 34, 35, 100, 200, 500, 10000]
            ]
            self._send_json(
                {
                    "project": "All Odd Zeta Values Are Linearly Independent Over Q — Lean 4 Formalization",
                    "author": "Prince Anand",
                    "toolchain": (ROOT_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()
                    if (ROOT_DIR / "lean-toolchain").exists()
                    else "leanprover/lean4:v4.15.0",
                    "file_count": len(files),
                    "total_declarations": total_decls,
                    "total_sorries": total_sorries,
                    "files": files,
                    "asymptotic_table": table4,
                }
            )
            return

        if path == "/api/compute-bounds":
            try:
                n_val = int(qs.get("n", ["2"])[0])
                n_val = max(1, min(100000, n_val))
            except ValueError:
                n_val = 2
            self._send_json(compute_closed_form_bounds(n_val))
            return

        if path == "/api/central-factorial":
            try:
                m_val = max(1, min(50, int(qs.get("m", ["3"])[0])))
                r_val = max(0, min(60, int(qs.get("r", ["1"])[0])))
            except ValueError:
                m_val, r_val = 3, 1
            self._send_json(compute_central_factorial_payload(m_val, r_val))
            return

        if path == "/" or path == "/index.html":
            self._send_file(STATIC_DIR / "index.html")
            return

        if path.startswith("/static/"):
            rel = path[len("/static/") :]
            target = (STATIC_DIR / rel).resolve()
            if str(target).startswith(str(STATIC_DIR.resolve())):
                self._send_file(target)
                return

        self.send_error(404, "Not Found")


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 3000))
    server = ThreadingHTTPServer(("0.0.0.0", port), AppRequestHandler)
    print(f"Serving Odd Zeta Formalization Verification Server on http://0.0.0.0:{port}", flush=True)
    server.serve_forever()
