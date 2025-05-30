function openLeanPlayground(button) {
  const codeBlock = button.previousElementSibling.querySelector("code");
  const code = codeBlock.innerText;

  const playgroundUrl = "https://leanprover.github.io/lean4play/#code=" + encodeURIComponent(code);

  window.open(playgroundUrl, '_blank');
}
