window.MathJax = {
  loader: {load: ["[tex]/mathtools"]},
  tex: {
    inlineMath: [["$", "$"], ["\\(", "\\)"]],
    displayMath: [["$$", "$$"], ["\\[", "\\]"]],
    packages: ["base", "ams", "mathtools"],
    processEscapes: true,
    processEnvironments: true
    macros: {
      type: ["{{\\text{Type}\ #1}}", 1],
      pie: ["{{\\Pi\\ (#1)\\ (#2)}}", 2],
      turnstile: ["{{\\Gamma \\vdash #1 : #2}}", 2]
    }
  },
  options: {
    skipHtmlTags: ["script", "noscript", "style", "textarea", "pre"],
    ignoreHtmlClass: "tex2jax_ignore"
  }
};
