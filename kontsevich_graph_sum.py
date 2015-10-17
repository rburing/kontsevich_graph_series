r"""
Kontsevich graph sums

"""
from sage.kontsevich_graph_series.kontsevich_graph import KontsevichGraph
from sage.structure.element import ModuleElement
from sage.modules.module import Module
from sage.symbolic.ring import is_SymbolicExpressionRing

class KontsevichGraphSum(ModuleElement):
    def __init__(self, parent, terms):
        """
        Kontsevich graph sum.
        """
        if terms == 0:
            terms = []
        if not isinstance(terms, list):
            raise TypeError('Input must be a list of terms.')
        if not all(isinstance(t, tuple) and len(t) == 2 for t in terms):
            raise TypeError('Terms must be (coefficient, graph) tuples.')
        if not all(c in parent.base_ring() and isinstance(g, KontsevichGraph)
                   and getattr(g, '_immutable', False) for (c,g) in terms):
            raise TypeError('Coefficients must be in base ring, and ' +
                            'graphs must be immutable KontsevichGraphs.')
        self._terms = terms
        ModuleElement.__init__(self, parent=parent)
    def _rmul_(self, c):
        return self.parent()([(c*d,g) for (d,g) in self._terms])
    def _add_(self, other):
        return self.parent()(self._terms + other._terms)
    def __cmp__(self, other):
        return cmp(self._terms, other._terms)
    def __hash__(self):
        return hash(tuple(self._terms))
    def reduce(self):
        graphs = set(g for (c,g) in self._terms)
        coefficient = lambda g: sum(c for (c,h) in self._terms if h == g)
        self._terms = [(coefficient(g), g) for g in graphs]
    def _repr_(self):
        self.reduce()
        parenthesize = lambda c: str(c)
        if is_SymbolicExpressionRing(self.base_ring()):
            from sage.symbolic.operators import add_vararg
            is_sum = lambda x: self.base_ring()(x).operator() == add_vararg
            parenthesize = lambda c: '(%s)' % c if is_sum(c) else c
        return ' + '.join('%s*(%s)' % (parenthesize(c), g) for (c,g) in self._terms)

class KontsevichGraphSums(Module):
    Element = KontsevichGraphSum
    def _element_constructor_(self, terms):
        if isinstance(terms, KontsevichGraphSum): terms = terms._terms
        return self.element_class(self, terms)
    def __cmp__(self, other):
        if not isinstance(other, KontsevichGraphSums):
            return cmp(type(other), KontsevichGraphSums)
        return cmp(self.base_ring(), other.base_ring())
    def _an_element_(self):
        return self.element_class(self, [])
