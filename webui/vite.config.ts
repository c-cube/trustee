import solid from "vite-plugin-solid";
import { defineConfig } from "vitest/config";

const backend = "http://127.0.0.1:8089";

const proxied = [
  "/static",
  "/blob",
  "/render",
  "/render_seq",
  "/c",
  "/eval",
  "/proof",
  "/thy",
  "/art",
  "/stats",
];

export default defineConfig({
  plugins: [solid()],
  build: {
    lib: {
      entry: "src/entry.ts",
      formats: ["es"],
      fileName: () => "trustee-ui.js",
    },
    sourcemap: true,
  },
  server: {
    proxy: Object.fromEntries(proxied.map((p) => [p, { target: backend }])),
  },
  test: {
    environment: "node",
    include: ["tests/**/*.spec.ts"],
  },
});
