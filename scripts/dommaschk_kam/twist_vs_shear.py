"""UNTRUSTED numerics (N-48 claim C1). Usage: python twist_vs_shear.py WORK_DIR (the --work of run.py).
 Compare the ELP-S twist T of a Dommaschk flow torus with the
prediction T = +- cc^2/(2 pi^2) * d iota/dV, V = volume enclosed per field period (phi in [0, pi)),
cc = field-line-time normalisation returned by twist.elps_twist (omega_s = cc*(omega/pi, 1/pi)).
Also report d iota/d Phi (toroidal flux) and dPhi/dV for reference."""
import glob, json, os, sys
import numpy as np
KAM = os.path.dirname(os.path.abspath(__file__)); WORK = sys.argv[1]
sys.path.insert(0, KAM)
import dfield, dioph, torus as T, twist as TW

ex = dfield.ExactField(dfield.TARGET); ev = dfield.Evaluator(ex)

def volume(a, b, N, M, Nt=256, Nphi=128):
    th, ph, R, z, Rt, Rp, zt, zp = TW.grid_eval(a, b, N, M, Nt, Nphi)
    # V = int_0^pi dphi oint R^2/2 dz ; theta-mean * 2pi, phi-mean * pi
    return float(np.mean(R**2/2*zt)*2*np.pi*np.pi)

def neighbours(a, b, N, M, iota, delta):
    out = []
    for dl in (-delta, delta):
        g = T.Galerkin(ev, N, M, iota + dl)
        a1, b1, h = T.newton_double(g, a.copy(), b.copy(), log=lambda s: None)
        out.append((iota + dl, a1, b1, h[-1]))
    return out

for spec in ['A', 'B', 'C']:
    files = sorted(glob.glob(os.path.join(WORK, f'double_{spec}_N*_M*_f3.npz')),
                   key=lambda p: int(p.split('_N')[1].split('_')[0]))
    d = np.load(files[-1]); a, b = d['a'], d['b']
    N = int(files[-1].split('_N')[1].split('_')[0]); M = int(files[-1].split('_M')[1].split('_')[0])
    iota = -float(dioph.iota_abs(spec))
    Tt, Trel, inv, ws = TW.elps_twist(ev, a, b, N, M, iota)
    cc = ws[1]*np.pi
    row = dict(spec=spec, N=N, M=M, iota=iota, T=Tt, cc=cc, invariance=inv)
    for delta in (2e-4, 1e-4):
        nb = neighbours(a, b, N, M, iota, delta)
        V = [volume(x[1], x[2], N, M) for x in nb]
        Ph = [TW.flux(ev, x[1], x[2], N, M) for x in nb]
        dI = nb[1][0] - nb[0][0]
        div = dI/(V[1] - V[0]); dif = dI/(Ph[1] - Ph[0])
        pred = cc**2/(2*np.pi**2)*div
        row[f'delta{delta}'] = dict(diota_dV=div, diota_dPhi=dif, dPhi_dV=(Ph[1]-Ph[0])/(V[1]-V[0]),
                                    T_pred=pred, ratio_T_over_pred=Tt/pred,
                                    newton=[x[3] for x in nb])
    print(json.dumps(row, indent=1))
