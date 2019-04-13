build:
	yarn elm make src/Main.elm --output out.js
	echo "this.Elm.Main.init();" >>out.js
	tput reset
	@node out.js
