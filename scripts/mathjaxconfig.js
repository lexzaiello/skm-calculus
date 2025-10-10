window.MathJax = {
  loader: {load: ['[tex]/mathtools']},
  tex: {
    inlineMath: [['$', '$'], ['\\(', '\\)']],
    displayMath: [['$$', '$$'], ['\\[', '\\]']],
    packages: ['base', 'ams', 'mathtools'],
    macros: {
      type: ['{\\text{Type}\\ #1}', 1],
      pie: ['\\Pi\\ (#1)\\ (#2)', 2],
      turnstile: ['\\Gamma \\vdash #1 : #2', 2]
    }
  }
};

(function() {
  const script = document.createElement('script');
  script.src = 'https://cdn.jsdelivr.net/npm/mathjax@4/tex-mml-chtml.js';
  script.async = false;
  document.head.appendChild(script);
})();
