<!--
This file is part of CPAchecker,
a tool for configurable software verification:
https://cpachecker.sosy-lab.org

SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>

SPDX-License-Identifier: Apache-2.0
-->

CPAchecker Installation
=======================

For information on how to run CPAchecker, see [`README.md`](README.md).

Note that right now CPAchecker works best on Linux (64-bit x86)
because not for all external dependencies native binaries
are supplied for other platforms.
So some configurations or features might not work on other platforms.


Install CPAchecker -- Binary
----------------------------

1. Install a Java Runtime Environment which is at least Java 17 compatible.
   One Linux we recommend to install a package from your distribution
   (Ubuntu: `sudo apt install openjdk-17-jre`),
   on other platforms you can for example get one from
   [Adoptium](https://adoptium.net/temurin/releases/?version=17).
   If you have multiple JVMs installed, consider making this the default JVM,
   otherwise you will need to specify the JVM when running CPAchecker.
   (Ubuntu: `sudo update-alternatives --config java`)

2. Extract the content of the CPAchecker zip or tar file into a directory of your choice.


Install CPAchecker -- Docker
----------------------------
We provide an Ubuntu-based Docker image with a CPAchecker binary under the following name:
```
registry.gitlab.com/sosy-lab/software/cpachecker
```
You can specify the tag `:latest` for the latest release,
or the tag `:dev` for the latest development version.
Inside the Docker image, CPAchecker is installed under `/cpachecker`,
and you can mount your current working directory to `/workdir`
in order to provide input files to CPAchecker and retrieve output files.
Recommended command line:
```
docker run -v $(pwd):/workdir -u $UID:$GID registry.gitlab.com/sosy-lab/software/cpachecker ...CPAchecker arguments...
```


Install CPAchecker -- Source
----------------------------

1. Install a Java SDK which is Java 17 compatible (later versions are also fine).
   Most people use OpenJDK, e.g., from their distribution
   (Ubuntu: `sudo apt-get install openjdk-17-jdk`)
   or from [Adoptium](https://adoptium.net/temurin/releases/?version=17).
   If you have multiple JDKs installed, make sure that the commands `java`
   and `javac` call the respective Java 17 binaries (or a later version),
   so put them in your PATH or change the system-wide default JDK.
   (Ubuntu: `sudo update-alternatives --config java; sudo update-alternatives --config javac`)

2. Install `ant` (version 1.10.x or later is recommended).
   (Ubuntu: `sudo apt-get install ant`)

3. Install Subversion.
   (Ubuntu: `sudo apt-get install subversion`)

4. Checkout CPAchecker from SVN repository.
   URL: https://svn.sosy-lab.org/software/cpachecker/trunk
   URL (read-only GIT mirror): https://github.com/sosy-lab/cpachecker

5. Run `ant` in CPAchecker directory to build CPAchecker.
   When building CPAchecker for the first time, this will automatically
   download all needed libraries.
   If you experience problems, please check the following items:
   - If you have incompatible versions of some libraries installed on your system,
     the build might fail with NoSuchMethodErrors or similar exceptions.
     In this case, run `ant -lib lib/java/build`.
   - If the build fails due to compile errors in AutomatonScanner.java or FormulaScanner.java,
     you have a too-old version of JFlex installed.
     In this case, run `ANT_TASKS=none ant` to use our supplied JFlex
     instead of the one installed on the system.
   - If the build fails because the class `org.apache.ivy.ant.BuildOBRTask` cannot be found,
     this is probably caused by an old Ivy version installed on your system.
     Please try uninstalling Ivy.

(For building CPAchecker within Eclipse, cf. [`doc/Developing.md`](doc/Developing.md).)
