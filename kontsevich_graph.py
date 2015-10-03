r"""
Kontsevich graphs

"""
from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.structure.factorization import Factorization
from sage.rings.integer import Integer

class KontsevichGraph(DiGraph):
    def __init__(self, *args, **kwargs):
        """
        Kontsevich graph.

        INPUT:

         - All the usual arguments to DiGraph.
         - ``ground_vertices`` -- a list of vertices to be ground vertices.

        OUTPUT:

        A KontsevichGraph object.

        EXAMPLES::

            sage: KontsevichGraph(ground_vertices=[])
            Kontsevich graph with 0 vertices on 0 ground vertices
            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F', 'G'])
            Kontsevich graph with 1 vertices on 2 ground vertices
        """
        kwargs['weighted'] = True               # edge labels are important in equality testing
        copying = len(args) == 1 and isinstance(args[0], KontsevichGraph)
        if not copying and not 'ground_vertices' in kwargs:
            raise TypeError('KontsevichGraph() needs keyword argument ground_vertices, or an existing KontsevichGraph as the first argument.')
        if 'ground_vertices' in kwargs:
            ground_vertices = kwargs['ground_vertices']
            del kwargs['ground_vertices']
        else:                                   # copying
            ground_vertices = args[0].ground_vertices()

        super(KontsevichGraph, self).__init__(*args, **kwargs)
        self.ground_vertices(ground_vertices)
    
    def ground_vertices(self, vs=None):
        """
        Returns or sets the ground vertices.

        INPUT:

         - ``vs`` -- if not None, then this becomes the new list of ground vertices.

        EXAMPLES::

            sage: KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F', 'G'])
            sage: KG.ground_vertices()
            ['F', 'G']
            sage: KG.ground_vertices(['F'])
            ['F']

        .. NOTE::
            
            Ground vertices of immutable KontsevichGraphs can also be changed,
            as a consequence of the implementation.
        """
        if not vs is None:
            if not isinstance(vs, list):
                raise ValueError('Input must be a list of vertices.')
            if not all(v in self for v in vs):
                raise ValueError('Input vertices must exist in the Kontsevich graph.')
            if not all(self.out_degree(v) == 0 for v in vs):
                raise ValueError('Prospective ground vertices must have out-degree zero.')
            self.set_vertices({v : None for v in self})
            self.set_vertices({v : n for (v,n) in zip(vs, range(0,len(vs)))})
        return [k for (k,v) in sorted(self.get_vertices().items()) if not v is None]
    
    def internal_vertices(self):
        """
        Returns the internal vertices.
        """
        return sorted([v for v in self if not v in self.ground_vertices()])

    def _repr_(self):
        n = len(self.internal_vertices())
        m = len(self.ground_vertices())
        return 'Kontsevich graph with %d vertices on %d ground vertices' % (n, m)
        
    def show(self, *args, **kwargs):
        """
        Shows the Kontsevich graph.
        """
        if not 'edge_labels' in kwargs:
            kwargs['edge_labels'] = True        # show edge labels by default
        return super(KontsevichGraph, self).show(*args, **kwargs)

    def union(self, other):
        """
        Returns the union of self and other.
        """
        G = super(KontsevichGraph, self).union(other)
        immutable = getattr(self, '_immutable', False) and getattr(other, '_immutable', False)
        ground_vertices = list(set(self.ground_vertices()) | set(other.ground_vertices()))
        return KontsevichGraph(G, ground_vertices=ground_vertices, immutable=immutable)

    def normalize_vertex_labels(self):
        """
        Label internal vertices 1, ...,  n.
        Label external vertices F, G, ...
        """
        relabeling = {v : n + 1 for (n, v) in enumerate(self.internal_vertices())}
        relabeling.update({v : chr(70 + n) for (n, v) in enumerate(self.ground_vertices())})
        self.relabel(relabeling)

    def internal_vertices_normalized(self):
        """
        Whether the internal vertices are equal to 1, ..., n.
        """
        n = len(self.internal_vertices())
        return self.internal_vertices() == range(1,n+1)

    def internal_vertex_relabelings(self):
        """
        Yields all possible internal vertex relabelings as Kontsevich graphs.
        """
        assert self.internal_vertices_normalized(), "Internal vertices should be normalized."

        for sigma in SymmetricGroup(self.internal_vertices()):
            G = DiGraph(self, weighted=True, immutable=False)
            G.relabel(lambda v: sigma(v) if v in self.internal_vertices() else v)
            yield KontsevichGraph(G, ground_vertices=self.ground_vertices(), immutable=True)

    def __eq__(self, other):
        """
        Compare self and other for equality.
        Kontsevich graphs are considered equal if the underlying DiGraphs differ only in their internal vertex labeling.
        """
        assert self.internal_vertices_normalized(), "Internal vertices should be normalized."

        if len(self) != len(other): return False
        if len(self.internal_vertices()) != len(other.internal_vertices()): return False
        for KG in other.internal_vertex_relabelings():
            if DiGraph(self, weighted=True) == DiGraph(KG, weighted=True): return True
        return False

    def __mul__(self, other):
        """
        Returns the product of self and other.

        EXAMPLES::

            sage: KG1 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G'])
            sage: KG2 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G'])
            sage: KG1*KG1 == KG2
            True
        """
        assert isinstance(other, KontsevichGraph)
        assert self.ground_vertices() == other.ground_vertices()
        assert self.internal_vertices_normalized() and other.internal_vertices_normalized()
        sigma = lambda v: v+len(self.internal_vertices()) if v in other.internal_vertices() else v
        multiplicand = KontsevichGraph(other, ground_vertices=other.ground_vertices())
        multiplicand.relabel(sigma)
        return self.union(multiplicand)

    def __pow__(self, exponent):
        """
        Returns the product of ``self`` with itself, ``exponent`` times.

        EXAMPLES::

            sage: KG1 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G'])
            sage: KG1^3
            Kontsevich graph with 3 vertices on 2 ground vertices
        """
        assert self.internal_vertices_normalized(), "Internal vertices should be normalized."
        assert isinstance(exponent, int) or isinstance(exponent, Integer)
        assert exponent >= 0
        product = KontsevichGraph({v : {} for v in self.ground_vertices()}, ground_vertices=self.ground_vertices())
        for n in range(0,exponent):
            factor = KontsevichGraph(self, ground_vertices=self.ground_vertices()) # a copy
            sigma = lambda v: v+n*len(self.internal_vertices()) if v in self.internal_vertices() else v
            factor.relabel(sigma)
            product = product.union(factor)
        return product

    def factor(self):
        """
        Returns the prime factorization of the graph.

        EXAMPLES::

            sage: KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G'])
            sage: KG.factor()
            (Kontsevich graph with 1 vertices on 2 ground vertices)^2

        ALGORITHM::

            Delete ground vertices; the remaining connected components correspond to the prime factors.
        """
        floorless = DiGraph(self, weighted=True, immutable=False)
        floorless.delete_vertices(self.ground_vertices())
        factors = []
        for C in floorless.connected_components():
            P = self.subgraph(vertices=C + self.ground_vertices())
            P_KG = KontsevichGraph(P, ground_vertices=self.ground_vertices())
            P_KG.normalize_vertex_labels()
            factors.append(P_KG)
        return Factorization([(f,1) for f in factors])
        
    def is_prime(self):
        """
        Whether the graph is prime.

        EXAMPLES::

            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G']).is_prime()
            True
            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, ground_vertices=['F','G']).is_prime()
            False

        ALGORITHM::

            Delete ground vertices; count connected components (which correspond to prime factors).
        """
        floorless = DiGraph(self, immutable=False)
        floorless.delete_vertices(self.ground_vertices())
        return len(floorless.connected_components()) == 1
