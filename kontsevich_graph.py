r"""
Kontsevich graphs

"""
from sage.graphs.digraph import DiGraph

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

        immutable = kwargs.get('immutable', False)
        kwargs['immutable'] = False
        super(KontsevichGraph, self).__init__(*args, **kwargs)
        self.ground_vertices(ground_vertices)
        setattr(self, '_immutable', immutable)
    
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
        """
        if not vs is None:
            if getattr(self, '_immutable', False):
                raise NotImplementedError('The ground vertices of an immutable KontsevichGraph do not change.')
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
        return [v for v in self if not v in self.ground_vertices()]

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
