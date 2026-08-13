library: index
	lake build

audit:
	python3 scripts/aiprover_audit.py
	python3 scripts/aiprover_audit.py THEOREM_TIERS.md
	python3 scripts/aiprover_audit.py GroundZero/Exercises/README.md

index:
	lake script run updateIndex

clean:
	lake clean

all: index library
	lake script run updateDependencyMap pictures/dependency-map.svg
