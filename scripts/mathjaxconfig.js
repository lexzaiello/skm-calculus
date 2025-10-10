window.MathJax = {
  loader: {load: ["[tex]/mathtools"]},
  tex: {
    inlineMath: [["$", "$"], ["\\(", "\\)"]],
    displayMath: [["$$", "$$"], ["\\[", "\\]"]],
    packages: ["base", "ams", "mathtools"],
    processEnvironments: true,
    macros: {
      type: ["{\\text{Type}\\ #1}", 1],
      pie: ["\\Pi\\ (#1)\\ (#2)", 2],
      turnstile: ["\\Gamma \\vdash #1 : #2", 2]
    }
  },
  options: {
    skipHtmlTags: ["script", "noscript", "style", "textarea", "pre"],
    ignoreHtmlClass: "tex2jax_ignore"
  }
};

(function() {
  const script = document.createElement("script");
  script.src = "https://cdn.jsdelivr.net/npm/mathjax@4/tex-mml-chtml.js";
  script.async = true;
  document.head.appendChild(script);
})();
