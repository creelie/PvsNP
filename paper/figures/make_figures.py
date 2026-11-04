"""Draw the figures of the paper as 3D PNG images (200 dpi)."""
import csv, collections, os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection, Line3DCollection

HERE = os.path.dirname(os.path.abspath(__file__))
LIT = os.path.join(HERE, '..', '..', 'literature')
PAL = ['#2a78d6', '#eb6834', '#1baf7a', '#eda100', '#e87ba4', '#008300', '#6250d6', '#e34948']
INK, INK2, GRID = '#0b0b0b', '#52514e', '#d9d8d4'
plt.rcParams.update({'font.family': 'DejaVu Serif', 'font.size': 9, 'axes.edgecolor': INK2,
                     'axes.labelcolor': INK, 'xtick.color': INK2, 'ytick.color': INK2})

def clean3d(ax):
    for a in (ax.xaxis, ax.yaxis, ax.zaxis):
        a.pane.set_facecolor((1, 1, 1, 0)); a.pane.set_edgecolor(GRID)
        a._axinfo['grid']['color'] = GRID; a._axinfo['grid']['linewidth'] = 0.5

def save(fig, name):
    fig.savefig(os.path.join(HERE, name + '.png'), dpi=200, bbox_inches='tight', facecolor='white')
    plt.close(fig)

def bars3d(ax, xs, ys, zs, colors, dx=0.6, dy=0.5):
    for x, y, z, c in zip(xs, ys, zs, colors):
        if z > 0:
            ax.bar3d(x - dx / 2, y - dy / 2, 0, dx, dy, z, color=c, edgecolor='white', linewidth=0.4, shade=True)

def box(ax, x, y, z, dx, dy, dz, c, alpha=0.9):
    X = [x, x + dx]; Y = [y, y + dy]; Z = [z, z + dz]
    v = np.array([[X[i], Y[j], Z[k]] for i in (0, 1) for j in (0, 1) for k in (0, 1)])
    faces = [[0, 1, 3, 2], [4, 5, 7, 6], [0, 1, 5, 4], [2, 3, 7, 6], [0, 2, 6, 4], [1, 3, 7, 5]]
    pc = Poly3DCollection([v[f] for f in faces], facecolor=c, edgecolor='white', linewidth=0.6, alpha=alpha)
    ax.add_collection3d(pc)

# ---------------------------------------------------------------- oblique prisms on a 2D canvas
import matplotlib.colors as mcolors
def shade(c, f):
    r, g, b = mcolors.to_rgb(c); return (r * f, g * f, b * f)

def prism(ax, x, y, w, h, d, c, zorder=2):
    """Box with front face [x,x+w]x[y,y+h], extruded by depth d at 30 degrees."""
    dx, dy = d * 0.866, d * 0.5
    front = [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]
    top = [(x, y + h), (x + w, y + h), (x + w + dx, y + h + dy), (x + dx, y + h + dy)]
    side = [(x + w, y), (x + w + dx, y + dy), (x + w + dx, y + h + dy), (x + w, y + h)]
    for poly, f in ((side, 0.55), (top, 0.8), (front, 1.0)):
        ax.add_patch(plt.Polygon(poly, closed=True, facecolor=shade(c, f), edgecolor='white', lw=0.6, zorder=zorder))

def canvas(w, h, xlim, ylim):
    fig = plt.figure(figsize=(w, h)); ax = fig.add_axes([0, 0, 1, 1]); ax.set_axis_off()
    ax.set_xlim(*xlim); ax.set_ylim(*ylim); ax.set_aspect('equal'); return fig, ax

# ---------------------------------------------------------------- landscape
def landscape():
    levels = ['linear $cn$', 'barely superlinear', r'$n^{1+\epsilon}$', r'$n^{3-o(1)}$', 'superpolynomial', 'exponential']
    data = [('fan-in two\nin P', 1, 0), ('fan-in two\nin $\\mathsf{E^{NP}}$', 2, 0), ('gates of\nTheorem B', 2, 0),
            ('de Morgan\nformulas', 4, 1), ('monotone\ncircuits', 6, 1),
            ('any gates,\ndepth $d$', 2, 2), ('threshold,\ndepth $d$', 3, 2), ('$\\mathsf{ACC}^0$', 5, 2),
            ('$\\mathsf{AC}^0[p]$', 6, 2), ('$\\mathsf{AC}^0$', 6, 2)]
    cols = [PAL[1], PAL[0], PAL[2]]
    U, W, S = 0.62, 0.62, 1.0   # unit height, bar width, spacing
    fig = plt.figure(figsize=(7.2, 3.6)); ax = fig.add_axes([0.16, 0.2, 0.82, 0.68]); ax.set_axis_off()
    n = len(data); ax.set_xlim(-0.3, n * S + 0.2); ax.set_ylim(-0.05, 6 * U + 0.55); ax.set_aspect('equal')
    for i in range(1, 7):
        ax.plot([0, n * S], [i * U, i * U], color=GRID, lw=0.5, zorder=0)
        ax.text(-0.15, i * U, levels[i - 1], ha='right', va='center', fontsize=7, color=INK2)
    ax.plot([0, n * S], [0, 0], color=INK2, lw=0.8, zorder=1)
    for j, (lab, h, k) in enumerate(data):
        prism(ax, j * S + 0.12, 0, W, h * U, 0.3, cols[k])
        ax.text(j * S + 0.12 + W / 2, -0.12, lab, ha='center', va='top', fontsize=6.6, color=INK)
    from matplotlib.patches import Patch
    fig.legend(handles=[Patch(color=cols[0], label='unbounded depth, general gates'),
                        Patch(color=cols[1], label='unbounded depth, restricted'),
                        Patch(color=cols[2], label='bounded depth')],
               loc='upper center', ncol=3, fontsize=7, frameon=False, bbox_to_anchor=(0.55, 1.0))
    save(fig, 'fig_landscape')

# ---------------------------------------------------------------- pipeline
def pipeline():
    steps = [('input $1^n$ of\n$H\\in\\mathsf{NTIME}(2^n)$', PAL[0]), ('local reduction:\nindex $\\mapsto$ clause', PAL[1]),
             ('guess a circuit $E$\nwith at most\n$s_n$ wires', PAL[2]), ('test circuit $\\mathcal{T}$:\n$\\Delta_n$, three copies\nof $E$, check gate', PAL[6]),
             ('Theorem A:\nis $\\#\\mathcal{T}=0$?', PAL[3]), ('$H\\in\\mathsf{NTIME}(2^{n/2})$:\ncontradiction', PAL[7])]
    fig, ax = canvas(7.2, 1.9, (-0.2, 18.2), (-2.6, 2.1))
    for k, (lab, c) in enumerate(steps):
        x = 3.05 * k
        prism(ax, x, 0, 2.1, 0.7, 0.55, c)
        ax.text(x + 1.05, -0.2, lab, ha='center', va='top', fontsize=7, color=INK)
        if k < len(steps) - 1:
            ax.annotate('', xy=(x + 3.0, 0.42), xytext=(x + 2.6, 0.42),
                        arrowprops=dict(arrowstyle='-|>', color=INK2, lw=1.0, mutation_scale=8))
    ax.text(9.0, 1.55, 'the $\\mathsf{NTIME}(2^{n/2})$ machine of Theorem B on input $1^n$', ha='center', fontsize=7.5, color=INK2)
    save(fig, 'fig_pipeline')

# ---------------------------------------------------------------- blocks
def blocks():
    fig, ax = canvas(6.6, 3.0, (-1.2, 12.4), (-1.3, 5.0))
    k, K = 4, 6
    rx, ry = 4.6, 3.1
    prism(ax, rx, ry, 2.0, 0.55, 0.45, PAL[0], zorder=3)
    ax.text(rx + 1.2, ry + 1.05, 'root $r_g$:  $z=\\varphi\\left(\\sum_j(\\mathrm{val}(e_j)-K2^\\beta)\\right)$',
            ha='center', fontsize=8, color=INK)
    for j in range(k):
        x0 = j * 3.1
        c = PAL[j % 3 + 1]
        for t in range(K):
            ax.plot([x0 + 0.35 * t + 0.1, x0 + 1.0], [0, 1.1], color=GRID, lw=0.7, zorder=1)
            ax.add_patch(plt.Circle((x0 + 0.35 * t + 0.1, 0), 0.09, color=INK2, zorder=2))
        prism(ax, x0 + 0.3, 1.1, 1.4, 0.45, 0.35, c, zorder=3)
        ax.text(x0 + 1.0, 1.32, f'$v_{{g,{j+1}}}$', ha='center', va='center', fontsize=7.5, color='white', zorder=4)
        for t in range(3):
            ax.plot([x0 + 0.75 + 0.25 * t, rx + 0.45 + 0.35 * j + 0.1 * t], [1.55 + 0.02, ry],
                    color=c, lw=0.9, zorder=2)
    ax.text(5.4, -0.55, '$f$ inputs in blocks of at most $K=\\lfloor s^{4/5}\\rfloor$', ha='center', va='top', fontsize=8, color=INK2)
    ax.text(9.4, 2.55, '$b=\\beta+\\lceil\\log K\\rceil+2$ edges\nfrom each block to the root', ha='left', fontsize=7.5, color=INK2)
    save(fig, 'fig_blocks')

# ---------------------------------------------------------------- network
def network():
    fig = plt.figure(figsize=(6.4, 4.4)); ax = fig.add_subplot(projection='3d'); ax.set_axis_off()
    inputs = {f'x{i}': np.array((i * 1.5, 0.0, 0.0)) for i in range(1, 5)}
    gates = {'g1': np.array((2.2, 0.5, 1.4)), 'g2': np.array((5.0, -0.5, 1.4)), 'g3': np.array((3.6, 0.0, 2.8))}
    pred = {'g1': ['x1', 'x2', 'x3'], 'g2': ['x2', 'x3', 'x4'], 'g3': ['g1', 'g2', 'x3']}
    hub = dict(inputs)
    for g, p in gates.items():
        hub[g] = p + np.array((0.0, 0.0, 0.55))
    edges = []
    for g, ps in pred.items():
        for p in ps:
            edges.append((hub[p], gates[g]))
    for g in gates:
        edges.append((gates[g], hub[g]))
    pin = hub['g3'] + np.array((0.0, 0.0, 0.6)); edges.append((hub['g3'], pin))
    ax.add_collection3d(Line3DCollection([[a, b] for a, b in edges], colors=INK2, linewidths=0.9))
    mids = np.array([(a + b) / 2 for a, b in edges])
    ax.scatter(mids[:, 0], mids[:, 1], mids[:, 2], s=16, c='white', edgecolors=INK2, depthshade=False, linewidths=0.8)
    hp = np.array(list(hub.values()))
    ax.scatter(hp[:, 0], hp[:, 1], hp[:, 2], s=60, c=PAL[2], depthshade=False, edgecolors='white')
    gp = np.array(list(gates.values()))
    ax.scatter(gp[:, 0], gp[:, 1], gp[:, 2], s=240, c=PAL[0], depthshade=False, edgecolors='white', linewidths=1.5)
    ax.scatter([pin[0]], [pin[1]], [pin[2]], s=80, c=PAL[7], marker='s', depthshade=False)
    for name, p in gates.items():
        ax.text(p[0] + 0.3, p[1], p[2] - 0.1, '$g_' + name[1] + '$', fontsize=8, color=INK)
    for name, p in inputs.items():
        ax.text(p[0], p[1], p[2] - 0.45, '$x_' + name[1] + '$', fontsize=8, color=INK, ha='center')
    ax.text(pin[0] + 0.3, pin[1], pin[2], 'pin $(0,1)$', fontsize=8, color=INK)
    ax.set_xlim(1, 6.5); ax.set_ylim(-1, 1); ax.set_zlim(-0.5, 3.6)
    ax.view_init(elev=12, azim=-78); ax.set_box_aspect((1.6, 0.6, 1.2))
    ax.text2D(0.0, 0.96, 'gate vertex $[z=g(y)]$', color=PAL[0], transform=ax.transAxes, fontsize=8)
    ax.text2D(0.0, 0.91, 'equality vertex', color=PAL[2], transform=ax.transAxes, fontsize=8)
    ax.text2D(0.0, 0.86, 'subdivision vertex', color=INK2, transform=ax.transAxes, fontsize=8)
    save(fig, 'fig_network')

# ---------------------------------------------------------------- claims
def claims():
    rows = list(csv.DictReader(open(os.path.join(LIT, 'woeginger_claims.csv'))))
    verdicts = ['Equal', 'Not equal', 'Unprovable', 'Undecidable']
    names = ['claims of $\\mathsf{P}=\\mathsf{NP}$', 'claims of $\\mathsf{P}\\neq\\mathsf{NP}$', 'unprovable', 'undecidable']
    cols = [PAL[0], PAL[1], PAL[2], PAL[6]]
    years = list(range(1986, 2017))
    cnt = collections.Counter((r['claim'], int(r['year'])) for r in rows)
    U, S = 0.32, 0.42
    fig = plt.figure(figsize=(7.2, 3.3)); ax = fig.add_axes([0.07, 0.14, 0.92, 0.72]); ax.set_axis_off()
    top = max(sum(cnt[(v, y)] for v in verdicts) for y in years)
    ax.set_xlim(-0.6, len(years) * S + 0.3); ax.set_ylim(-0.1, (top + 1) * U); ax.set_aspect('equal')
    for t in range(0, top + 1, 2):
        ax.plot([0, len(years) * S], [t * U, t * U], color=GRID, lw=0.5, zorder=0)
        ax.text(-0.12, t * U, str(t), ha='right', va='center', fontsize=7, color=INK2)
    for j, y in enumerate(years):
        base = 0
        for v, c in zip(verdicts, cols):
            h = cnt[(v, y)]
            if h:
                prism(ax, j * S + 0.05, base * U, 0.26, h * U, 0.12, c, zorder=2 + base)
                base += h
        if y % 5 == 0:
            ax.text(j * S + 0.18, -0.12, str(y), ha='center', va='top', fontsize=7, color=INK2)
    from matplotlib.patches import Patch
    fig.legend(handles=[Patch(color=c, label=n) for c, n in zip(cols, names)], loc='upper center', ncol=4,
               fontsize=7, frameon=False, bbox_to_anchor=(0.53, 1.0))
    fig.text(0.035, 0.5, 'entries per year', rotation=90, va='center', fontsize=7.5, color=INK2)
    save(fig, 'fig_claims')

# ---------------------------------------------------------------- catalogue
def catalogue():
    core = {'cs.CC', 'cs.DS', 'cs.LO', 'cs.DM', 'math.CO', 'math.LO', 'cs.IT', 'math.AG', 'math.RT', 'cs.CR'}
    rows = [r for r in csv.DictReader(open(os.path.join(LIT, 'arxiv_catalogue.csv'))) if r['primary_category'] in core]
    topics = ['natural proofs', 'meta-complexity', 'proof complexity', 'circuit lower bound', 'P vs NP', 'ETH/SETH']
    names = ['natural proofs', 'meta-complexity', 'proof complexity', 'circuit lower bounds', 'P vs NP', 'ETH, SETH']
    cnt = collections.Counter()
    for r in rows:
        y = int(r['first_version'][:4])
        for t in r['matched'].split(';'):
            cnt[(t.strip(), y)] += 1
    years = list(range(2000, 2027))
    fig = plt.figure(figsize=(7.4, 4.4)); ax = fig.add_subplot(projection='3d'); clean3d(ax)
    for ti, t in enumerate(topics):
        bars3d(ax, years, [ti] * len(years), [cnt[(t, y)] for y in years], [PAL[[6, 4, 3, 2, 1, 0][ti]]] * len(years), dx=0.7, dy=0.55)
    ax.set_yticks(range(len(topics))); ax.set_yticklabels(names, fontsize=6.5)
    ax.set_xlabel('year of first version', fontsize=8); ax.set_zlabel('papers', fontsize=8)
    ax.set_zticks([0, 20, 40, 60, 80]); ax.view_init(elev=24, azim=-60); ax.set_box_aspect((2.6, 1.7, 0.9))
    save(fig, 'fig_catalogue')

# ---------------------------------------------------------------- taper
def taper():
    a, u, h = 12, 8, 3
    fig = plt.figure(figsize=(6.8, 4.0)); ax = fig.add_subplot(projection='3d'); clean3d(ax)
    lv = np.arange(0, a + 1)
    tap = [h * max(0, u - i) for i in lv]; flat = [h * u if i < u else 0 for i in lv]
    bars3d(ax, lv, [0] * len(lv), tap, [PAL[0]] * len(lv), dx=0.6, dy=0.5)
    bars3d(ax, lv, [1] * len(lv), flat, [PAL[1]] * len(lv), dx=0.6, dy=0.5)
    ax.set_yticks([0, 1]); ax.set_yticklabels(['tapered $q(i)=h(u-i)^+$', 'flat $q_*$'], fontsize=7)
    ax.set_xlabel('two-adic level $i$ of the node', fontsize=8); ax.set_zlabel('multiplicity', fontsize=8)
    ax.view_init(elev=22, azim=-55); ax.set_box_aspect((2.2, 1, 0.9))
    save(fig, 'fig_taper')

for f in (landscape, pipeline, network, blocks, claims, catalogue, taper):
    f()
print('ok')
