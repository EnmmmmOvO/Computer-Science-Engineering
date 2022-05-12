
var cy = cytoscape({
  container: document.getElementById('cy'),

  elements: elems,

  style: [
    {
      selector: 'node',
      style: {
        'label': 'data(id)',
        'width': 15,
        'height': 15,
        'background-color': '#666',
        'border-width': 2,
        'border-color': 'black',
      },
    },

    {
      selector: 'node.power-plant',
      style: {
        'background-color': 'yellow',
      },
    },

    {
      selector: 'edge',
      style: {
        'width': 3,
        'line-color': '#ccc',
        'curve-style': 'bezier'
      },
    },
  ],

  layout: {
    name: 'preset',
  },

  autolock: true,
  wheelSensitivity: 0.2,
});
