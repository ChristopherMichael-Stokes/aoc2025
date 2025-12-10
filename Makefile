ALL: new_inputs

.venv/bin/python: pyproject.toml
	uv sync
	touch $@

day := 0
day_str = day$(shell printf "%02d" $(day))
solution_template := _solution_template.py
day_url = https://adventofcode.com/2025/day/$(day)


# Set up empty solutions director.  Usage:
# Make the day02/ folder structure & open up problem statement in background.
# $make day=2 
new_inputs: .venv/bin/python
	mkdir -p $(day_str)
	touch $(day_str)/inputs.txt
	touch $(day_str)/sample.txt
	cp $(solution_template) $(day_str)/solution.py

	@if [ "$$(uname)" = "Darwin" ]; then \
		open -g "$(day_url)"; \
	fi


.PHONY:
	new_inputs

