all:
	$(MAKE) -C 2ltt

docker:
	docker build -t lean-image .

run-image:
	docker run -it lean-image

clean:
	$(MAKE) clean -C 2ltt
