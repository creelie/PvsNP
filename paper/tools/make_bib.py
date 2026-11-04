"""Write paper/part7_bib.tex from literature/crossref_records.json plus manual entries."""
import json, re, sys, os
here = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(here, '..', '..', 'literature', 'crossref_records.json')))
TITLE = {
 'Aar16': r'$\mathsf P\overset{?}{=}\mathsf{NP}$',
 'BGS75': r'Relativizations of the $\mathcal P=?\mathcal{NP}$ question',
 'LY22': r'$3.1n-o(n)$ circuit lower bounds for explicit functions',
 'Ajt83': r'$\Sigma^1_1$-formulae on finite structures',
 'CSS18': r'Average-case lower bounds and satisfiability algorithms for small threshold circuits',
 'MS01': r'Geometric complexity theory I: an approach to the P vs.\ NP and related problems',
 'PPSZ05': r'An improved exponential-time algorithm for $k$-SAT',
 'IW97': r'$P=BPP$ if $E$ requires exponential circuits: derandomizing the XOR lemma',
 'Mul12': r'The GCT program toward the P vs.\ NP problem',
 'Gas19': r'Guest column: the third P $=?$ NP poll',
 'Her14': r'3-SAT faster and simpler---Unique-SAT bounds for PPSZ hold in general',
 'GKST18': r'Gate elimination: circuit size lower bounds and \#SAT upper bounds',
 'Sch80': r'A $3n$-lower bound on the network complexity of Boolean functions',
 'Blu84': r'A Boolean function requiring $3n$ network size',
 'IM02': r'An explicit lower bound of $5n-o(n)$ for Boolean circuits',
 'IP01': r'On the complexity of $k$-SAT',
 'Sch99': r'A probabilistic algorithm for $k$-SAT and constraint satisfaction problems',
 'FGHK16': r'A better-than-$3n$ lower bound for the circuit complexity of an explicit function',
 'AKS04': r'PRIMES is in P',
 'Tod91': r'PP is as hard as the polynomial-time hierarchy',
 'Wil14': r'Nonuniform ACC circuit lower bounds',
 'Wil13': r'Improving exhaustive search implies superpolynomial lower bounds',
 'Din07': r'The PCP theorem by gap amplification',
 'RSW22': r'On the range avoidance problem for circuits',
 'Raz87': r'Lower bounds on the size of bounded depth circuits over a complete basis with logical addition',
 'Hak85': r'The intractability of resolution',
 'BSW01': r'Short proofs are narrow---resolution made simple',
 'KW16': r'Super-linear gate and super-quadratic wire lower bounds for depth-two and depth-three threshold circuits',
 'Has98': r'The shrinkage exponent of de Morgan formulas is $2$',
 'Tal14': r'Shrinkage of de Morgan formulae by spectral techniques',
 'Ros08': r'On the constant-depth complexity of $k$-clique',
 'Kor21': r'The hardest explicit construction',
 'IKW02': r'In search of an easy witness: exponential time vs.\ probabilistic polynomial time',
 'MW20': r'Circuit lower bounds for nondeterministic quasi-polytime from a new easy witness lemma',
 'HMPST93': r'Threshold circuits of bounded depth',
 'Coo71': r'The complexity of theorem-proving procedures',
 'Hir22': r'NP-hardness of learning programs and partial MCSP',
 'ILW23': r'Indistinguishability obfuscation, range avoidance, and bounded arithmetic',
 'ST13': r'A satisfiability algorithm and average-case hardness for formulas over the full binary basis',
 'CIP06': r'A duality between clause width and clause density for SAT',
 'Ser': '',
}
AUTH = {
 'Has86': ['J. H{\\aa}stad'], 'Has98': ['J. H{\\aa}stad'], 'Pud94': ['P. Pudl{\\\'a}k'],
 'Yao85': ['A. C.-C. Yao'], 'Raz87': ['A. A. Razborov'], 'Smo87': ['R. Smolensky'],
 'Sch99': ['U. Sch{\\"o}ning'], 'Imp95': ['R. Impagliazzo'], 'Tar88': ['{\\\'E}. Tardos'],
 'Che11': ['D. Yu. Cherukhin'], 'Zak83': ['S. {\\v Z}{\\\'a}k'], 'Kra19': ['J. Kraj{\\\'\\i}{\\v c}ek'],
 'BIP19': ['P. B{\\"u}rgisser', 'C. Ikenmeyer', 'G. Panova'], 'Rag88': ['P. Raghavan'],
 'CHOPRS22': ['L. Chen', 'S. Hirahara', 'I. C. Oliveira', 'J. Pich', 'N. Rajgopal', 'R. Santhanam'],
 'OS18': ['I. C. Oliveira', 'R. Santhanam'], 'AK10': ['E. Allender', 'M. Kouck{\\\'y}'],
 'Wil05': ['R. Williams'], 'Wil14': ['R. Williams'], 'Wil13': ['R. Williams'], 'Wil14b': ['R. Williams'],
 'Wil14c': ['R. Williams'], 'Wil16': ['R. R. Williams'], 'Wil25': ['R. R. Williams'],
 'MW20': ['C. D. Murray', 'R. R. Williams'], 'KW16': ['D. M. Kane', 'R. Williams'],
 'MS01': ['K. D. Mulmuley', 'M. Sohoni'], 'Mul12': ['K. D. Mulmuley'],
 'vzGG13': ['J. von zur Gathen', 'J. Gerhard'],
}
CONT = [
 ('Journal of Computer and System Sciences', 'J. Comput. System Sci.'),
 ('SIAM Journal on Computing', 'SIAM J. Comput.'), ('SIAM Journal on Discrete Mathematics', 'SIAM J. Discrete Math.'),
 ('Journal of the ACM', 'J. ACM'), ('Theoretical Computer Science', 'Theoret. Comput. Sci.'),
 ('Communications of the ACM', 'Commun. ACM'), ('Transactions of the American Mathematical Society', 'Trans. Amer. Math. Soc.'),
 ('Canadian Journal of Mathematics', 'Canad. J. Math.'), ('Bell System Technical Journal', 'Bell System Tech. J.'),
 ('Annals of Pure and Applied Logic', 'Ann. Pure Appl. Logic'), ('Mathematical Systems Theory', 'Math. Systems Theory'),
 ('Mathematical Notes of the Academy of Sciences of the USSR', 'Math. Notes Acad. Sci. USSR'),
 ('ACM Transactions on Computation Theory', 'ACM Trans. Comput. Theory'), ('Information and Control', 'Inform. and Control'),
 ('Theory of Computing', 'Theory Comput.'), ('Journal of Symbolic Logic', 'J. Symbolic Logic'),
 ('Journal of the American Mathematical Society', 'J. Amer. Math. Soc.'), ('computational complexity', 'Comput. Complexity'),
 ('Annals of Mathematics', 'Ann. of Math. (2)'), ('Discrete Mathematics and Applications', 'Discrete Math. Appl.'),
 ('Discrete Mathematics', 'Discrete Math.'), ('ACM SIGACT News', 'ACM SIGACT News'), ('Combinatorica', 'Combinatorica'),
]
BOOK = {
 'AB09': 'Cambridge University Press, Cambridge, 2009', 'Juk12': 'Algorithms Combin. \\textbf{27}, Springer, Heidelberg, 2012',
 'Kra19': 'Encyclopedia Math. Appl. \\textbf{170}, Cambridge University Press, Cambridge, 2019',
 'vzGG13': 'third edition, Cambridge University Press, Cambridge, 2013',
}
YEAR = {'Blu84': 1984, 'BIP19': 2019, 'LST21': 2021, 'Kor21': 2021, 'Sch99': 1999, 'Imp95': 1995, 'CIP06': 2006}
PROC = {
 'Coo71': 'Proceedings of the Third Annual ACM Symposium on Theory of Computing (STOC 1971)',
 'Sip92': 'Proceedings of the 24th Annual ACM Symposium on Theory of Computing (STOC 1992)',
 'Kar72': 'Complexity of Computer Computations, R. E. Miller and J. W. Thatcher (eds.), Plenum Press, New York',
 'Aar16': 'Open Problems in Mathematics, J. F. Nash, Jr. and M. Th. Rassias (eds.), Springer, Cham',
 'Has86': 'Proceedings of the 18th Annual ACM Symposium on Theory of Computing (STOC 1986)',
 'Smo87': 'Proceedings of the 19th Annual ACM Symposium on Theory of Computing (STOC 1987)',
 'Val79a': 'Proceedings of the 11th Annual ACM Symposium on Theory of Computing (STOC 1979)',
 'KC00': 'Proceedings of the 32nd Annual ACM Symposium on Theory of Computing (STOC 2000)',
 'Wil14b': 'Proceedings of the 46th Annual ACM Symposium on Theory of Computing (STOC 2014)',
 'KW16': 'Proceedings of the 48th Annual ACM Symposium on Theory of Computing (STOC 2016)',
 'LY22': 'Proceedings of the 54th Annual ACM Symposium on Theory of Computing (STOC 2022)',
 'ILW23': 'Proceedings of the 55th Annual ACM Symposium on Theory of Computing (STOC 2023)',
 'CHR24': 'Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024)',
 'Li24': 'Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024)',
 'Wil25': 'Proceedings of the 57th Annual ACM Symposium on Theory of Computing (STOC 2025)',
 'IW97': 'Proceedings of the 29th Annual ACM Symposium on Theory of Computing (STOC 1997)',
 'Ros08': 'Proceedings of the 40th Annual ACM Symposium on Theory of Computing (STOC 2008)',
 'Yao85': '26th Annual Symposium on Foundations of Computer Science (FOCS 1985), IEEE',
 'PPST83': '24th Annual Symposium on Foundations of Computer Science (FOCS 1983), IEEE',
 'Sch99': '40th Annual Symposium on Foundations of Computer Science (FOCS 1999), IEEE',
 'San10': '51st Annual IEEE Symposium on Foundations of Computer Science (FOCS 2010)',
 'IPS13': '54th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2013)',
 'Tal14': '55th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2014)',
 'FGHK16': '57th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2016)',
 'Hir18': '59th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2018)',
 'OS18': '59th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2018)',
 'LST21': '62nd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2021)',
 'Kor21': '62nd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2021)',
 'Hir22': '63rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2022)',
 'RSW22': '63rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2022)',
 'Imp95': 'Proceedings of the Tenth Annual Structure in Complexity Theory Conference, IEEE, 1995',
 'CIP06': '21st Annual IEEE Conference on Computational Complexity (CCC 2006)',
 'Wil14c': '29th IEEE Conference on Computational Complexity (CCC 2014)',
 'Val77': 'Mathematical Foundations of Computer Science 1977, Lecture Notes in Comput. Sci. \\textbf{53}, Springer, Berlin',
 'IM02': 'Mathematical Foundations of Computer Science 2002, Lecture Notes in Comput. Sci. \\textbf{2420}, Springer, Berlin',
 'CIP09': 'Parameterized and Exact Computation (IWPEC 2009), Lecture Notes in Comput. Sci. \\textbf{5917}, Springer, Berlin',
 'JMV15': 'Automata, Languages, and Programming (ICALP 2015), Part I, Lecture Notes in Comput. Sci. \\textbf{9134}, Springer, Berlin',
}
def initials(n):
    n = ' '.join(n.split())
    parts = n.split(' ')
    last = parts[-1]; first = parts[:-1]
    if last.lower() in ('jr.', 'jr'):
        last = parts[-2] + ', Jr.'; first = parts[:-2]
    out = []
    for f in first:
        if f.lower() in ('van', 'von', 'de', 'der', 'zur'):
            out.append(f); continue
        if '-' in f:
            out.append('-'.join(x[0] + '.' for x in f.split('-') if x)); continue
        out.append(f[0] + '.' if not f.endswith('.') or len(f) > 2 else f)
    return ' '.join(out + [last])
def tex(s):
    s = s.replace('&', '\\&').replace('#', '\\#').replace('—', '---').replace('–', '--')
    s = s.replace('ö', '{\\"o}').replace('ü', '{\\"u}').replace('é', "{\\'e}").replace('á', "{\\'a}").replace('í', "{\\'\\i}").replace('Ž', '{\\v Z}').replace('ž','{\\v z}').replace('č','{\\v c}')
    return s
def andjoin(a):
    return a[0] if len(a) == 1 else ', '.join(a[:-1]) + ' and ' + a[-1]
def sentence(t):
    t = ' '.join(re.sub('<[^>]+>', '', t).split())
    return t
items = {}
for k, v in d.items():
    au = AUTH.get(k) or [tex(initials(a)) for a in v['authors']]
    t = TITLE.get(k) or tex(sentence(v['title']))
    yr = YEAR.get(k, v['year'])
    pg = (v['page'] or '').replace('-', '--')
    doi = v['doi']
    if k in BOOK:
        body = f"\\emph{{{t}}}, {BOOK[k]}."
    elif k in PROC:
        body = f"\\emph{{{t}}}, in: {PROC[k]}, {yr}, pp.~{pg}." if 'Springer' not in PROC[k] or k=='Aar16' or True else ''
        if k in ('Imp95',):
            body = f"\\emph{{{t}}}, in: {PROC[k]}, pp.~{pg}."
    else:
        c = v['container']
        for a, b in CONT:
            if c == a: c = b; break
        vol = f" \\textbf{{{v['volume']}}}" if v['volume'] else ''
        iss = f", no.~{v['issue']}" if v['issue'] and v['issue'] != '0' else ''
        pp = f", {pg}" if pg else ''
        if k == 'Din07': pp = ', Art.~12'
        if k == 'MW20': pp = ', STOC18-300--STOC18-322'
        body = f"\\emph{{{t}}}, {c}{vol} ({yr}){iss}{pp}."
    items[k] = f"{andjoin(au)}, {body} \\href{{https://doi.org/{doi}}}{{doi:{doi.replace('_', chr(92) + '_').replace('#', chr(92) + '#').replace('%', chr(92) + '%')}}}"
M = {
 'Cai07': r"J.-Y. Cai, \emph{$\mathrm{S}_2^p\subseteq\mathrm{ZPP}^{\mathrm{NP}}$}, J. Comput. System Sci. \textbf{73} (2007), no.~1, 25--35. \href{https://doi.org/10.1016/j.jcss.2003.07.015}{doi:10.1016/j.jcss.2003.07.015}",
 'Yan91': r"M. Yannakakis, \emph{Expressing combinatorial optimization problems by linear programs}, J. Comput. System Sci. \textbf{43} (1991), no.~3, 441--466. \href{https://doi.org/10.1016/0022-0000(91)90024-Y}{doi:10.1016/0022-0000(91)90024-Y}",
 'GJ79': r"M. R. Garey and D. S. Johnson, \emph{Computers and Intractability: A Guide to the Theory of NP-Completeness}, W. H. Freeman, San Francisco, 1979.",
 'ILPS14': r"R. Impagliazzo, S. Lovett, R. Paturi and S. Schneider, \emph{0-1 integer linear programming with a linear number of constraints}, preprint (2014), \href{https://arxiv.org/abs/1401.5512}{arXiv:1401.5512}.",
 'Lev73': r"L. A. Levin, \emph{Universal sequential search problems}, Problemy Peredachi Informatsii \textbf{9} (1973), no.~3, 115--116 (in Russian); English translation in Problems Inform. Transmission \textbf{9} (1973), 265--266.",
 'OAI26': r"OpenAI, \emph{The exponential time hypothesis is false}, preprint, 25 October 2026, \url{https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf}.",
 'Wig19': r"A. Wigderson, \emph{Mathematics and Computation: A Theory Revolutionizing Technology and Science}, Princeton University Press, Princeton, 2019.",
 'Woe16': r"G. J. Woeginger, \emph{The P-versus-NP page}, \url{https://wscor.win.tue.nl/woeginger/P-versus-NP.htm}, last updated 2016.",
 'Clay': r"Clay Mathematics Institute, \emph{P vs NP}, Millennium Prize Problems, official problem description by S. Cook, \url{https://www.claymath.org/millennium/p-vs-np/}.",
 'ECCC': r"Electronic Colloquium on Computational Complexity, \url{https://eccc.weizmann.ac.il/}.",
 'Zoo': r"S. Aaronson et al., \emph{The Complexity Zoo}, \url{https://complexityzoo.net/Complexity_Zoo}.",
 'BhaHex26': r"D. Bhattacharjee, \emph{Subexponential weighted counting and exact optimisation}, HexagonMath preprint 2610.00594v1 (2026), \url{https://hexagonmath.org/2610.00594v1}.",
 'Bha26eth': r"D. Bhattacharjee, \emph{Source and verification code for the paper Subexponential Weighted Counting and Exact Optimisation}, Zenodo, release v1.4.0 (2026). \href{https://doi.org/10.5281/zenodo.23718560}{doi:10.5281/zenodo.23718560}",
 'Bha26weil': r"D. Bhattacharjee, \emph{LaTeX source and verification code for the paper Algebraic Loci of Weil Classes on Abelian Varieties}, Zenodo, release v5.1.0 (2026). \href{https://doi.org/10.5281/zenodo.23227940}{doi:10.5281/zenodo.23227940}",
 'Bha26bsd': r"D. Bhattacharjee, \emph{The $p$-primary part of the Tate--Shafarevich group in ranks three to six: paper, data and certificates}, Zenodo, release v1.0.2 (2026). \href{https://doi.org/10.5281/zenodo.23933270}{doi:10.5281/zenodo.23933270}",
}
items.update(M)
order = sorted(items, key=lambda k: k.lower())
with open(os.path.join(here, '..', 'part7_bib.tex'), 'w') as f:
    f.write('\\begingroup\\raggedright\\small\n\\begin{thebibliography}{CHOPRS22}\n')
    for k in order:
        f.write(f'\\bibitem[{k}]{{{k}}} {items[k]}\n')
    f.write('\\end{thebibliography}\n\\endgroup\n')
print(len(order))
