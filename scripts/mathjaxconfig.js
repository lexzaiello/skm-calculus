window.MathJax = {
  loader: {load: ['[tex]/mathtools']},
  tex: {
    inlineMath:  [['$', '$'], ['\\(', '\\)']],
    displayMath: [['$$', '$$'], ['\\[', '\\]']],
    packages:    ['base', 'ams', 'mathtools'],
    macros: {
      type:         ['{\\text{Type}\\ #1}', 1],
      pie:          ['\\Pi\\ (#1)', 1],
      piee:         ['\\Pi\\ (#1)\\ (#2)', 2],
      pieee:        ['\\Pi\\ (#1)\\ (#2)\\ (#3)', 3],
      turnstile:    ['{\\vdash #1 : #2}', 2],
      turnstilee:   ['\\vdash #1 : #2,\\ #3 : #4', 4],
      turnstileee:  ['\\vdash #1 : #2,\\ #3 : #4,\\ #5 : #6', 6],
      turnstileeee: ['\\vdash #1 : #2,\\ #3 : #4,\\ #5 : #6,\\ #7 : #8', 8]
    }
  }
};

(function() {
  const script = document.createElement('script');
  script.src = 'https://cdn.jsdelivr.net/npm/mathjax@4/tex-mml-chtml.js';
  script.async = false;
  document.head.appendChild(script);
})();
