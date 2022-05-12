
var cy = cytoscape({
  container: document.getElementById('cy'),

  elements: elems,

  style: [
    {
      selector: 'node',
      style: {
        'label': 'data(id)',
        'height': 48,
        'width': 48,
        'background-color': '#666',
        'color': 'white',
        'font-size': 28,
        'text-halign': 'center',
        'text-valign': 'center',
      },
    },

    {
      selector: 'edge',
      style: {
        'curve-style': 'haystack',
      },
    },
    
    {
      selector: 'edge[weight]',
      style: {
        'label': 'data(weight)',
        'width': 2,
        'color': 'blue',
        'font-size': 28,
        'line-color': 'black',
        'text-background-color': 'white',
        'text-background-opacity': 1,
        'text-background-padding': 5,
        'z-index': 2,
      }
    },
    
    {
      selector: 'edge.mst',
      style: {
        'width': 10,
        'line-color': '#60cc08',
        'z-index': 1,
      },
    },
  ],

  layout: {
    name: 'circle',
  },
  
  wheelSensitivity: 0.2,
});
