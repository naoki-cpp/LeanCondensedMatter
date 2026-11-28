export function createExplorerComposition(ui) {
  let page;
  let revision = 0;
  const graphPanel = ui.graph.closest(".graph-panel");

  function mount(tabSlot, controlsSlot, searchSlot = ui.controls) {
    if (ui.tabs.parentElement !== tabSlot) tabSlot.prepend(ui.tabs);
    if (ui.controls.parentElement !== controlsSlot) controlsSlot.append(ui.controls);
    if (ui.searchForm.parentElement !== searchSlot) searchSlot.prepend(ui.searchForm);
    ui.controlsHome.hidden = controlsSlot !== ui.controlsHome;
  }

  function replaceOverview(...content) {
    const focused = document.activeElement;
    ui.overview.replaceChildren(...content);
    mountOverview();
    if (focused?.isConnected && document.activeElement === document.body) {
      focused.focus({ preventScroll: true });
    }
  }

  function mountOverview() {
    mount(ui.overview.querySelector(".map-tabs-slot") ?? ui.controlsHome,
      ui.overview.querySelector(".map-controls-slot") ?? ui.controlsHome,
      ui.overview.querySelector(".map-search-slot") ?? ui.controls);
  }

  return {
    show(nextPage, importTitle, focusTarget) {
      revision += 1;
      const initial = page === undefined;
      page = nextPage;
      const imports = page === "imports";
      const overview = page === "overview";
      const selectedTab = imports ? ui.moduleImportsLink : ui.overviewLink;
      const focused = focusTarget ?? (ui.tabs.contains(document.activeElement) ? selectedTab : null);
      for (const tab of [ui.overviewLink, ui.moduleImportsLink]) {
        tab.setAttribute("aria-selected", String(tab === selectedTab));
        tab.tabIndex = tab === selectedTab ? 0 : -1;
      }
      const panel = imports ? ui.importsPanel : ui.declarationsPanel;
      if (ui.appShell.parentElement !== panel) panel.append(ui.appShell);
      ui.declarationsPanel.hidden = imports;
      ui.importsPanel.hidden = !imports;
      for (const className of ["import-map-panel", "explorer-map-theme", "explorer-map-frame"]) {
        graphPanel.classList.toggle(className, imports);
      }
      const { header, heading, status, tabs, search } = ui.importMapHeader;
      header.hidden = !imports;
      ui.importMapControls.hidden = !imports;
      if (imports) {
        heading.textContent = importTitle;
        if (ui.graphStatus.parentElement !== status) status.append(ui.graphStatus);
        mount(tabs, ui.importMapControls, search);
      } else {
        ui.graphToolbar.prepend(ui.graphStatus);
        if (overview) {
          if (!initial) mountOverview();
        } else mount(ui.controlsHome, ui.controlsHome);
      }
      ui.overview.hidden = !overview;
      ui.viewport.hidden = overview;
      ui.viewport.classList.toggle("explorer-map-stage", imports);
      ui.graphToolbar.hidden = overview;
      if (focused && document.activeElement === document.body) focused.focus({ preventScroll: true });
    },
    async renderOverview({ render, unavailable, failed }) {
      const request = ++revision;
      try {
        const build = await render();
        if (request !== revision || page !== "overview") return;
        if (build) replaceOverview(...build());
        else unavailable();
      } catch (error) {
        if (request !== revision || page !== "overview") return;
        failed(error);
      }
    },
    replaceOverview,
  };
}
