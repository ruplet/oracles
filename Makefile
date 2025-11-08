clean:
	find chapters -type f -name '*.aux' -print -delete
	rm driver.bcf driver.log driver.out driver.run.xml driver.toc driver.bbl driver.blg driver.synctex.gz  -f
