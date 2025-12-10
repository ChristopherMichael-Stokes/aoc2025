day := 0
day_str = day$(shell printf "%02d" $(day))
solution_template := _solution_template.py

new_inputs:
	mkdir $(day_str)
	touch $(day_str)/inputs.txt
	touch $(day_str)/sample.txt
	cp $(solution_template) $(day_str)/solution.py

.PHONY:
	new_inputs