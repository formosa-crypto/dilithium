all: sign-ct.ec

keygen-ct.ec:
	jasminc -CT -ec keygen -oec keygen-ct.ec ../src/keygen.jazz

sign-ct.ec:
	jasminc -CT -ec sign -oec sign-ct.ec ../src/sign.jazz

clean:
	rm -f Array*.ec WArray*.ec sign-ct.ec keygen.ec *.ec~ *.eco
