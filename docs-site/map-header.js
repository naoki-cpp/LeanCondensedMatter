export function createMapHeader(title = "", header = document.createElement("header")) {
  const row = document.createElement("div");
  row.className = "map-heading-row";
  const heading = document.createElement("h2");
  heading.className = "research-map-title";
  heading.tabIndex = -1;
  heading.textContent = title;
  const tabs = document.createElement("div");
  tabs.className = "map-tabs-slot";
  const search = document.createElement("div");
  search.className = "map-search-slot";
  const status = document.createElement("p");
  status.className = "research-map-declaration-count";
  row.append(heading, tabs);
  header.append(row, status, search);
  return { header, heading, status, tabs, search };
}
