r"""
Kontsevich star product

"""
from sage.kontsevich_graph_series.kontsevich_graph import KontsevichGraph, kontsevich_graphs
from sage.kontsevich_graph_series.kontsevich_graph_sum import KontsevichGraphSum
from sage.kontsevich_graph_series.kontsevich_graph_series import KontsevichGraphSeries
from sage.functions.other import factorial
from sage.rings.integer import Integer

# TODO: maybe a class for a weight system

def prime_weight(G, prime_weights):
    """
    Multiplicative weight of a prime Kontsevich graph.
    This function takes care of signs.

    INPUT:

    - ``G`` - prime KontsevichGraph
    - ``prime_weights`` - weights of prime graphs, modulo edge labeling and mirror images.
    """
    w = 1
    for g in [G, G.mirror_image()]:
        if g == G.mirror_image(): w *= (-1)**len(g.internal_vertices())
        for (h,s) in g.edge_relabelings(signs=True):
            if h in prime_weights:
                w *= s * prime_weights[h]
                return w
    return 0

def kontsevich_weight(G, prime_weights):
    """
    Multiplicative weight of an arbitrary Kontsevich graph.

    INPUT:

    - ``G`` - KontsevichGraph
    - ``prime_weights`` - weights of prime graphs, modulo edge labeling and mirror images.
    """
    import operator
    return reduce(operator.mul, [prime_weight(h, prime_weights)**n for (h,n) in G.factor()], 1)

def kontsevich_star_product_terms(K, prime_weights, precision):
    """
    Kontsevich star product terms in KontsevichGraphSums ``K`` up to order ``precision``.

    INPUT:

    - ``K`` - KontsevichGraphSums module.
    - ``prime_weights`` - weights of prime graphs, modulo edge labeling and mirror images.

    EXAMPLES::

        sage: K = KontsevichGraphSums(QQ);
        sage: weights = {}
        sage: weights[KontsevichGraph({'F' : {},'G' : {}}, ground_vertices=('F','G'), immutable=True)] = 1
        sage: weights[KontsevichGraph([(1, 'F', 'L'), (1, 'G', 'R')], ground_vertices=('F','G'), immutable=True)] = 1/2
        sage: weights[KontsevichGraph([(1, 2, 'R'), (1, 'F', 'L'), (2, 1, 'L'), (2, 'G', 'R')], ground_vertices=('F','G'), immutable=True)] = 1/24
        sage: weights[KontsevichGraph([(1, 2, 'R'), (1, 'F', 'L'), (2, 'F', 'L'), (2, 'G', 'R')], ground_vertices=('F','G'), immutable=True)] = 1/12
        sage: S.<h> = KontsevichGraphSeriesRng(K, star_product_terms = kontsevich_star_product_terms(K, weights, 2), default_prec = 2);
        sage: F = S(KontsevichGraph(('F',),immutable=True));
        sage: G = S(KontsevichGraph(('G',),immutable=True));
        sage: H = S(KontsevichGraph(('H',),immutable=True));
        sage: A = (F*G)*H - F*(G*H)
        sage: A.reduce()
        sage: len(A[2])  # three terms in the Jacobi identity
        3
    """
    series_terms = {0 : K([(prime_weights[KontsevichGraph(('F','G'), immutable=True)],
                            KontsevichGraph(('F','G'), immutable=True))])}
    for n in range(1, precision + 1):
        term = K(0)
        for graph in kontsevich_graphs(n, modulo_edge_labeling=True, positive_differential_order=True):
            coeff = kontsevich_weight(graph, prime_weights)*graph.multiplicity()/factorial(len(graph.internal_vertices()))
            if coeff != 0:
                term += K([(coeff, graph)])
        series_terms[n] = term
    return series_terms
