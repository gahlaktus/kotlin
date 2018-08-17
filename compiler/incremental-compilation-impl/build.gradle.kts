
plugins {
    kotlin("jvm")
    id("jps-compatible")
}

jvmTarget = "1.6"

dependencies {
    compile(project(":core:descriptors"))
    compile(project(":core:descriptors.jvm"))
    compile(project(":core:deserialization"))
    compile(project(":compiler:util"))
    compile(project(":compiler:frontend"))
    compile(project(":compiler:frontend.java"))
    compile(project(":compiler:cli"))
    compile(project(":kotlin-build-common"))
    compile(project(":compiler:daemon-common"))
    compileOnly(intellijCoreDep()) { includeJars("intellij-core") }
    compileOnly(intellijDep()) { includeJars("annotations") }

    testCompile(commonDep("junit:junit"))
    testCompile(projectDist(":kotlin-test:kotlin-test-junit"))
    testCompile(projectDist(":kotlin-stdlib"))
    testCompile(projectTests(":kotlin-build-common"))
    testCompile(projectTests(":compiler:tests-common"))
    testCompile(intellijCoreDep()) { includeJars("intellij-core") }
    testCompile(intellijDep()) { includeJars("annotations", "log4j", "jdom") }
}

sourceSets {
    "main" { projectDefault(project) }
    "test" { projectDefault(project) }
}

projectTest {
    workingDir = rootDir
}

testsJar()
