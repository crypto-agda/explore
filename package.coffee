fs   = require 'fs'
find = require 'find'
find.file /^[^.].*\.agda$/, '.', (files) ->
  fs.writeFile 'package.json', JSON.stringify
    name: "agda-explore"
    version: "0.0.1"
    description: "Big operators as exploration functions in Agda"
    main: "explore.agda"
    scripts:
      test: "echo \"Error: no test specified\" && exit 1"
    files: [ "README.md" ].concat(files)
    repository:
      type: "git"
      url: "https://github.com/crypto-agda/explore"
    keywords: [
      "agda"
      "library"
      "big-operators"
      "fold"
      "foldable"
    ]
    author: "Nicolas Pouillard"
    license: "BSD3"
    bugs:
      url: "https://github.com/crypto-agda/explore/issues"
    homepage: "https://github.com/crypto-agda/explore"
    dependencies:
      "agda-nplib": ">= 0.0.1"
    agda:
      include: [
        "."
        "lib"
      ]
