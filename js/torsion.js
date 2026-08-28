/*
 * Torsion point / division polynomial engine.
 *
 * Ports the recursive division-polynomial construction from the author's
 * Python tool (DividingPolynomial/dividingpolynomial.py) to run client-side,
 * then goes one step further: numerically solves the resulting kernel
 * polynomial for its roots and reports the corresponding torsion-point
 * coordinates, flagging the ones that land on Gaussian or Eisenstein
 * integers.
 *
 * Exact symbolic work (building psi_n, phi_n, and the composite kernel
 * polynomial) is done with BigInt fractions so there is no floating-point
 * error while the polynomials are constructed. Root-finding is necessarily
 * numeric (Durand-Kerner / Weierstrass method) since there is no general
 * closed form for the roots.
 */
(function (root) {
  "use strict";

  // ---------------- BigInt fraction arithmetic ----------------
  function bgcd(a, b) {
    a = a < 0n ? -a : a;
    b = b < 0n ? -b : b;
    while (b) { const t = a % b; a = b; b = t; }
    return a === 0n ? 1n : a;
  }
  function frac(n, d) {
    if (d === undefined) d = 1n;
    if (typeof n === "number") n = BigInt(n);
    if (typeof d === "number") d = BigInt(d);
    if (d < 0n) { n = -n; d = -d; }
    if (n === 0n) return { n: 0n, d: 1n };
    const g = bgcd(n, d);
    return { n: n / g, d: d / g };
  }
  const F0 = frac(0n), F1 = frac(1n), F2 = frac(2n), FHALF = frac(1n, 2n);
  function fadd(a, b) { return frac(a.n * b.d + b.n * a.d, a.d * b.d); }
  function fsub(a, b) { return frac(a.n * b.d - b.n * a.d, a.d * b.d); }
  function fmul(a, b) { return frac(a.n * b.n, a.d * b.d); }
  function fdiv(a, b) { return frac(a.n * b.d, a.d * b.n); }
  function fneg(a) { return { n: -a.n, d: a.d }; }
  function fisZero(a) { return a.n === 0n; }
  function fToNumber(a) { return Number(a.n) / Number(a.d); }
  function fToString(a) {
    if (a.d === 1n) return a.n.toString();
    return a.n.toString() + "/" + a.d.toString();
  }
  function fToLatex(a) {
    if (a.d === 1n) return a.n.toString();
    const neg = a.n < 0n;
    const nAbs = neg ? -a.n : a.n;
    return (neg ? "-" : "") + "\\frac{" + nAbs.toString() + "}{" + a.d.toString() + "}";
  }

  // ---------------- Polynomials over the fraction field (dense, index = power of x) ----------------
  function polyTrim(p) {
    let i = p.length - 1;
    while (i > 0 && fisZero(p[i])) i--;
    return p.slice(0, i + 1);
  }
  function polyIsZero(p) { return p.length === 1 && fisZero(p[0]); }
  const ZERO = [F0];
  function polyAdd(a, b) {
    const n = Math.max(a.length, b.length);
    const r = new Array(n);
    for (let i = 0; i < n; i++) r[i] = fadd(a[i] || F0, b[i] || F0);
    return polyTrim(r);
  }
  function polyNeg(a) { return a.map(fneg); }
  function polySub(a, b) { return polyAdd(a, polyNeg(b)); }
  function polyScale(a, s) { return polyTrim(a.map((c) => fmul(c, s))); }
  function polyMul(a, b) {
    if (polyIsZero(a) || polyIsZero(b)) return ZERO.slice();
    const r = new Array(a.length + b.length - 1).fill(null).map(() => F0);
    for (let i = 0; i < a.length; i++) {
      if (fisZero(a[i])) continue;
      for (let j = 0; j < b.length; j++) {
        if (fisZero(b[j])) continue;
        r[i + j] = fadd(r[i + j], fmul(a[i], b[j]));
      }
    }
    return polyTrim(r);
  }
  // Exact polynomial division a / d. Throws if it doesn't divide evenly.
  function polyDivExact(a, d) {
    d = polyTrim(d);
    let rem = a.slice();
    const dDeg = d.length - 1;
    const lead = d[dDeg];
    const qMap = {};
    for (;;) {
      rem = polyTrim(rem);
      if (polyIsZero(rem)) break;
      const rDeg = rem.length - 1;
      if (rDeg < dDeg) break;
      const c = fdiv(rem[rDeg], lead);
      const shift = rDeg - dDeg;
      qMap[shift] = c;
      for (let j = 0; j <= dDeg; j++) {
        const idx = j + shift;
        rem[idx] = fsub(rem[idx] || F0, fmul(c, d[j]));
      }
    }
    if (!polyIsZero(rem)) {
      throw new Error("polyDivExact: division left a nonzero remainder");
    }
    const maxDeg = Math.max(0, ...Object.keys(qMap).map(Number));
    const q = new Array(maxDeg + 1).fill(null).map(() => F0);
    for (const k in qMap) q[k] = qMap[k];
    return polyTrim(q);
  }
  function polyToLatex(p, varname) {
    varname = varname || "x";
    p = polyTrim(p);
    if (polyIsZero(p)) return "0";
    const terms = [];
    for (let power = p.length - 1; power >= 0; power--) {
      const c = p[power];
      if (fisZero(c)) continue;
      const neg = c.n < 0n;
      const absC = neg ? fneg(c) : c;
      let coeffStr;
      if (power === 0) coeffStr = fToLatex(absC);
      else if (absC.d === 1n && absC.n === 1n) coeffStr = "";
      else coeffStr = fToLatex(absC);
      let varStr = "";
      if (power === 1) varStr = varname;
      else if (power > 1) varStr = varname + "^{" + power + "}";
      const body = coeffStr + varStr || "1";
      terms.push({ neg, body });
    }
    let out = "";
    terms.forEach((t, i) => {
      if (i === 0) out += (t.neg ? "-" : "") + t.body;
      else out += (t.neg ? " - " : " + ") + t.body;
    });
    return out;
  }

  // ---------------- Y-split representation: value = P(x) + y*Q(x), with y^2 = curve(x) ----------------
  function yFromP(p) { return { P: polyTrim(p), Q: ZERO.slice() }; }
  function yZero() { return yFromP(ZERO.slice()); }
  function yAdd(a, b) { return { P: polyAdd(a.P, b.P), Q: polyAdd(a.Q, b.Q) }; }
  function ySub(a, b) { return { P: polySub(a.P, b.P), Q: polySub(a.Q, b.Q) }; }
  function yNeg(a) { return { P: polyNeg(a.P), Q: polyNeg(a.Q) }; }
  function yMul(a, b, curvePoly) {
    const PP = polyMul(a.P, b.P);
    const QQc = polyMul(polyMul(a.Q, b.Q), curvePoly);
    const P = polyAdd(PP, QQc);
    const Q = polyAdd(polyMul(a.P, b.Q), polyMul(b.P, a.Q));
    return { P, Q };
  }
  // Divide a pure-P value (no y component) by 2y, given the theoretical
  // guarantee that a.P is exactly divisible by curve(x). Returns a
  // y-multiple: P/(2y) = (P/curve) * y/2.
  function yDivBy2y(a, curvePoly) {
    if (!polyIsZero(a.Q)) {
      throw new Error("yDivBy2y: numerator was not a pure y-free polynomial");
    }
    const R = polyDivExact(a.P, curvePoly);
    return { P: ZERO.slice(), Q: polyScale(R, FHALF) };
  }

  // ---------------- Division polynomial recursion (psi_n, phi_n) ----------------
  function buildDivisionPolys(A, B) {
    const curvePoly = polyTrim([B, A, F0, F1]); // B + A x + 0 x^2 + 1 x^3
    const cache = {};
    function psi(n) {
      if (n in cache) return cache[n];
      let result;
      if (n === 0) {
        result = yZero();
      } else if (n === 1) {
        result = yFromP([F1]);
      } else if (n === 2) {
        result = { P: ZERO.slice(), Q: [F2] };
      } else if (n === 3) {
        const Asq = fmul(A, A);
        result = yFromP([fneg(Asq), fmul(frac(12n), B), fmul(frac(6n), A), F0, frac(3n)]);
      } else if (n === 4) {
        const A2 = fmul(A, A), A3 = fmul(A2, A), B2 = fmul(B, B);
        const inner = [
          fsub(fneg(fmul(frac(8n), B2)), A3),
          fneg(fmul(frac(4n), fmul(A, B))),
          fneg(fmul(frac(5n), A2)),
          fmul(frac(20n), B),
          fmul(frac(5n), A),
          F0,
          F1,
        ];
        result = { P: ZERO.slice(), Q: polyScale(inner, frac(4n)) };
      } else {
        const m = Math.floor(n / 2);
        if (n % 2 === 0) {
          const t1 = yMul(psi(m + 2), yMul(psi(m - 1), psi(m - 1), curvePoly), curvePoly);
          const t2 = yMul(psi(m - 2), yMul(psi(m + 1), psi(m + 1), curvePoly), curvePoly);
          const bracket = ySub(t1, t2);
          const val = yMul(psi(m), bracket, curvePoly);
          result = yDivBy2y(val, curvePoly);
        } else {
          const psiMcube = yMul(yMul(psi(m), psi(m), curvePoly), psi(m), curvePoly);
          const psiPcube = yMul(yMul(psi(m + 1), psi(m + 1), curvePoly), psi(m + 1), curvePoly);
          const t1 = yMul(psi(m + 2), psiMcube, curvePoly);
          const t2 = yMul(psi(m - 1), psiPcube, curvePoly);
          result = ySub(t1, t2);
        }
      }
      cache[n] = result;
      return result;
    }
    function phi(n) {
      if (n === 0) return yFromP([F1]);
      if (n === 1) return yFromP([F0, F1]);
      const xPoly = yFromP([F0, F1]);
      const psiN2 = yMul(psi(n), psi(n), curvePoly);
      const term1 = yMul(xPoly, psiN2, curvePoly);
      const term2 = yMul(psi(n + 1), psi(n - 1), curvePoly);
      return ySub(term1, term2);
    }
    return { psi, phi, curvePoly };
  }

  // ---------------- CM detection (mirrors the Python tool) ----------------
  function detectCM(A, B) {
    const aZero = fisZero(A), bZero = fisZero(B);
    if (bZero && !aZero) return { type: "gaussian", ring: "ℤ[i]", symbol: "i" };
    if (aZero && !bZero) return { type: "eisenstein", ring: "ℤ[ω]", symbol: "ω" };
    return { type: "none", ring: null, symbol: null };
  }

  // ---------------- Kernel polynomial for pi = n + m*s ----------------
  // Returns either { kind:'single', yp } for a plain psi_k (pure map, m=0 or n=0),
  // or { kind:'combo', cmType, term1, term2 } for a genuine pi = n + m*s.
  function computeKernel(nMap, mMap, A, B, cmType) {
    const { psi, phi, curvePoly } = buildDivisionPolys(A, B);
    if (mMap === 0 && nMap === 0) throw new Error("pi = 0 is not a valid map");
    if (mMap === 0) return { kind: "single", yp: psi(Math.abs(nMap)), curvePoly };
    if (nMap === 0) return { kind: "single", yp: psi(Math.abs(mMap)), curvePoly };
    if (cmType !== "gaussian" && cmType !== "eisenstein") {
      throw new Error("A composite map pi = n + m*s needs a curve with detected Gaussian or Eisenstein CM");
    }
    const n = Math.abs(nMap), m = Math.abs(mMap);
    const psiN = psi(n), psiM = psi(m), phiN = phi(n), phiM = phi(m);
    const term1 = yMul(phiN, yMul(psiM, psiM, curvePoly), curvePoly);
    const term2 = yMul(phiM, yMul(psiN, psiN, curvePoly), curvePoly);
    return { kind: "combo", cmType, term1, term2, curvePoly };
  }

  // Reduce a computeKernel() result down to a single x-polynomial ready for
  // root-finding. For the Gaussian/plain case the coefficients stay in
  // ℚ (represented as Fractions); for Eisenstein the coefficients are
  // a + b*omega pairs of Fractions.
  function extractCorePoly(kernelResult) {
    if (kernelResult.kind === "single") {
      const yp = kernelResult.yp;
      if (!polyIsZero(yp.Q) && !polyIsZero(yp.P)) {
        return { ok: false, reason: "The result has both a plain and a y-multiple part and can't be reduced to one variable automatically." };
      }
      if (!polyIsZero(yp.Q)) {
        return { ok: true, mode: "rational", poly: yp.Q, hasYFactor: true };
      }
      return { ok: true, mode: "rational", poly: yp.P, hasYFactor: false };
    }
    // combo
    const { cmType, term1, term2 } = kernelResult;
    if (!polyIsZero(term1.Q) || !polyIsZero(term2.Q)) {
      return { ok: false, reason: "The composite polynomial retained a y term and can't be reduced to one variable automatically." };
    }
    if (cmType === "gaussian") {
      return { ok: true, mode: "rational", poly: polyAdd(term1.P, term2.P), hasYFactor: false };
    }
    // eisenstein: value = term1.P - omega*term2.P = term1.P + omega*(-term2.P)
    return { ok: true, mode: "eisenstein", a: term1.P, b: polyNeg(term2.P), hasYFactor: false };
  }

  // ---------------- Complex arithmetic ----------------
  function cx(re, im) { return { re, im: im || 0 }; }
  function cAdd(a, b) { return cx(a.re + b.re, a.im + b.im); }
  function cSub(a, b) { return cx(a.re - b.re, a.im - b.im); }
  function cMul(a, b) { return cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re); }
  function cDiv(a, b) {
    const d = b.re * b.re + b.im * b.im;
    return cx((a.re * b.re + a.im * b.im) / d, (a.im * b.re - a.re * b.im) / d);
  }
  function cAbs(a) { return Math.hypot(a.re, a.im); }
  function cScale(a, s) { return cx(a.re * s, a.im * s); }
  function cSqrt(a) {
    const r = cAbs(a);
    if (r === 0) return cx(0, 0);
    const re = Math.sqrt((r + a.re) / 2);
    let im = Math.sqrt(Math.max(0, (r - a.re) / 2));
    if (a.im < 0) im = -im;
    return cx(re, im);
  }
  const OMEGA = cx(-0.5, Math.sqrt(3) / 2); // primitive cube root of unity

  function ratPolyToComplex(poly) {
    return poly.map((f) => cx(fToNumber(f), 0));
  }
  function eisensteinPolyToComplex(a, b) {
    const n = Math.max(a.length, b.length);
    const out = new Array(n);
    for (let i = 0; i < n; i++) {
      const av = a[i] ? fToNumber(a[i]) : 0;
      const bv = b[i] ? fToNumber(b[i]) : 0;
      out[i] = cAdd(cx(av, 0), cScale(OMEGA, bv));
    }
    return out;
  }

  // Durand-Kerner / Weierstrass simultaneous root finder for a complex
  // polynomial given as coefficients indexed by power (coeffs[deg] is the
  // leading coefficient).
  function findRoots(coeffs) {
    let c = coeffs.slice();
    while (c.length > 1 && cAbs(c[c.length - 1]) < 1e-12) c.pop();
    const deg = c.length - 1;
    if (deg <= 0) return [];
    const lead = c[deg];
    const mc = c.map((v) => cDiv(v, lead));
    function evalPoly(z) {
      let r = cx(0, 0);
      for (let i = deg; i >= 0; i--) r = cAdd(cMul(r, z), mc[i]);
      return r;
    }
    let roots = [];
    const seed = cx(0.4, 0.9);
    let p = cx(1, 0);
    for (let k = 0; k < deg; k++) { roots.push(p); p = cMul(p, seed); }
    for (let iter = 0; iter < 2000; iter++) {
      let maxDelta = 0;
      const next = roots.slice();
      for (let k = 0; k < deg; k++) {
        let denom = cx(1, 0);
        for (let j = 0; j < deg; j++) {
          if (j === k) continue;
          denom = cMul(denom, cSub(roots[k], roots[j]));
        }
        const delta = cDiv(evalPoly(roots[k]), denom);
        next[k] = cSub(roots[k], delta);
        const d = cAbs(delta);
        if (d > maxDelta) maxDelta = d;
      }
      roots = next;
      if (maxDelta < 1e-13) break;
    }
    return roots;
  }

  function nearestGaussianInt(z) {
    const a = Math.round(z.re), b = Math.round(z.im);
    return { a, b, err: Math.hypot(z.re - a, z.im - b) };
  }
  function nearestEisensteinInt(z) {
    const half = Math.sqrt(3) / 2;
    const b = z.im / half;
    const a = z.re + b / 2;
    const ra = Math.round(a), rb = Math.round(b);
    const recon = cAdd(cx(ra, 0), cScale(OMEGA, rb));
    return { a: ra, b: rb, err: Math.hypot(z.re - recon.re, z.im - recon.im) };
  }

  // ---------------- Top-level: solve for torsion point coordinates ----------------
  // curveAB: {A: Fraction, B: Fraction}; returns points with x, y1, y2 as
  // complex numbers plus Gaussian/Eisenstein recognition.
  function findTorsionPoints(core, A, B) {
    let complexCoeffs;
    if (core.mode === "rational") complexCoeffs = ratPolyToComplex(core.poly);
    else complexCoeffs = eisensteinPolyToComplex(core.a, core.b);

    const roots = findRoots(complexCoeffs);
    const Ac = cx(fToNumber(A), 0), Bc = cx(fToNumber(B), 0);
    const EPS = 1e-4;
    const points = roots.map((x) => {
      const rhs = cAdd(cAdd(cMul(cMul(x, x), x), cMul(Ac, x)), Bc);
      const y = cSqrt(rhs);
      const gx = nearestGaussianInt(x), ex = nearestEisensteinInt(x);
      const gy = nearestGaussianInt(y), ey = nearestEisensteinInt(y);
      let recognized = null;
      if (gx.err < EPS && gy.err < EPS) recognized = { type: "gaussian", x: gx, y: gy };
      else if (ex.err < EPS && ey.err < EPS) recognized = { type: "eisenstein", x: ex, y: ey };
      return { x, y, recognized };
    });
    return { core, points };
  }

  function fmtComplex(z, digits) {
    digits = digits === undefined ? 4 : digits;
    const EPS = Math.pow(10, -(digits + 1));
    const re = Math.abs(z.re) < EPS ? 0 : z.re;
    const im = Math.abs(z.im) < EPS ? 0 : z.im;
    if (im === 0) return re.toFixed(digits).replace(/\.?0+$/, "") || "0";
    const reStr = re === 0 ? "" : re.toFixed(digits).replace(/\.?0+$/, "");
    const sign = im < 0 ? "-" : (reStr ? "+" : "");
    const imAbs = Math.abs(im).toFixed(digits).replace(/\.?0+$/, "");
    return `${reStr}${reStr ? " " : ""}${sign}${sign ? " " : ""}${imAbs}i`;
  }

  const Torsion = {
    frac, fadd, fsub, fmul, fdiv, fneg, fisZero, fToNumber, fToString, fToLatex,
    polyTrim, polyIsZero, polyAdd, polySub, polyNeg, polyScale, polyMul, polyDivExact, polyToLatex,
    yFromP, yZero, yAdd, ySub, yNeg, yMul, yDivBy2y,
    buildDivisionPolys, detectCM, computeKernel, extractCorePoly,
    cx, cAdd, cSub, cMul, cDiv, cAbs, cSqrt, findRoots,
    nearestGaussianInt, nearestEisensteinInt, findTorsionPoints, fmtComplex,
  };

  if (typeof module !== "undefined" && module.exports) module.exports = Torsion;
  if (root) root.Torsion = Torsion;
})(typeof window !== "undefined" ? window : (typeof globalThis !== "undefined" ? globalThis : null));
