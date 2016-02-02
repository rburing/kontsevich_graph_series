from sage.misc.lazy_import import lazy_import

lazy_import('sage.kontsevich_graph_series.kontsevich_graph',
            ['KontsevichGraph', 'kontsevich_graphs'])
lazy_import('sage.kontsevich_graph_series.kontsevich_graph_sum',
            ['KontsevichGraphSum','KontsevichGraphSums'])
lazy_import('sage.kontsevich_graph_series.kontsevich_graph_series',
            ['KontsevichGraphSeries','KontsevichGraphSeriesRng'])
lazy_import('sage.kontsevich_graph_series.kontsevich_star_product',
            ['kontsevich_weight', 'kontsevich_star_product_terms'])
