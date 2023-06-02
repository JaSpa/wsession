# Intrinsically Typed Sessions With Callbacks

A paper with this title is conditionally accepted at ICFP 2023 and
what you have in your hands is the submitted version.
This directory contains the artifact accompanying the paper.

## Step-by-step Instructions

The first two steps are alternatives: either you start from the
zipfile (step 1) or you use the provided vm image (step 2).
After either step you should be in a directory called `src` and the
remaining steps assume that you issue commands from that directory. 

### 1 Using the zipfile

Prerequisites with suggested steps for debian Linux. In particular,
step 2 will take quite a while to complete.

1. make should be installed, e.g., by `apt-get install make`
2. agda-2.6.3 should be installed. I followed these instructions to do
  so for the image: https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html
3. clone the master branch of the agda standard library repository on github (https://github.com/agda/agda-stdlib)
4. point agda to this version of the standard library, rather than the
  default distributed with agda.
  
For step 4, assuming you cloned the
standard library in the directory `/home/artifact` do this:
```bash
cd
mkdir .agda
echo standard-library > defaults
echo /home/artifact/agda-stdlib/standard-library.agda-lib > libraries
```

To get agda in your executable path do this:

```bash
export PATH=~/.cabal/bin:$PATH
```

If you are here, you already unzipped the artifact, but there is a
surprise waiting in the `src` directory:

```bash
cd src
unzip supplement-icfp23.zip
```

### 2 Using the image

* start the image and log in as the `artifact` user

```bash
cd wsession/src
```

### 3 Type checking

```bash
make type-check
```

This step type checks the files that correspond to the different
versions of the session type library.

* `ST-finite-nonbranching.lagda` contains the material from section 2 of the
  paper *FINITE NON-BRANCHING SESSION TYPES* as well as the material
  from section 3 *SELECTION AND CHOICE"
* `ST-recursive.lagda` contains the material on recursive session
  types covered in section 4 *GOING IN CIRCLES*
* `ST-monadic.lagda` corresponds to section 5 *GOING MONADIC*
* `ST-indexed-contextfree.lagda` corresponds to section 6
  *CONTEXT-FREE SESSION TYPES*
* `ST-multichannel.lagda` corresponds to section 7 *HANDLING MULTIPLE
  CHANNELS*
* `ST-multichannel-finite-branching-recursion` is the extension of
  multichannel session types to finite branching and recursion that
  is proposed as an exercise to the reader in section 7: _In
  particular, we restrict to binary branching and leave the extension
  to finitary branching as well as the addition of recursion as an
  exercise to the reader._ This was done on request of a reviewer and
  a proper descripting will be incorporated in the final paper.
* `EX-multichannel.lagda` contains the main program for an actual
  executable that builds on top of the multichannel material in
  section 7. This was done after submitting the paper and it will find
  its place in the final paper.

### Running

There are two substeps: first compile the program and then run it.

```bash
make EX-multichannel
```

(Expect reams of output on the first round.)
The result of compilation is an executable called `EX-multichannel`.
To run it, you say

```bash
./EX-multichannel
```

The program consists of a server and a client that communicate on one
channel.  The important command structures are

* `system` creates a new channel and hands one end to the `client` and
  its other end to the `server`
* `server` receives two integers on channel `zero`, compares them for
  being less than or equal, and sends the result back on channel
  `zero`. It closes the channel and generates a boolean value (that
  gets ignored).
* `client` sends two integers (42 and 17) on channel `zero` (the other
  end of the channel available to the `server`), receives the boolean
  answer on channel `zero`, closes the channel, and passes the boolean
  answer as its final value.
* `main` starts the `system`, picks up the boolean returned from
  the `client`, and turns it into a string that is output on the
  console. If the program is not changed, the output will be `false`.
