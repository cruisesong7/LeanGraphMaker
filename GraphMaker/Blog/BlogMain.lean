import VersoBlog
import GraphMakerBlog.Main

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }}</title>
          {{← builtinHeader }}
        </head>
        <body>
          <main>
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </main>
        </body>
      </html>
    }}
  }

def graphMakerSite : Site := site GraphMakerBlog.Main

def main := blogMain theme graphMakerSite
