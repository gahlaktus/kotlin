
plugins {
    kotlin("jvm")
    id("jps-compatible")
}

jvmTarget = "1.6"

dependencies {
    compile(projectDist(":kotlin-stdlib"))
    compile(project(":core:deserialization"))
    compileOnly(intellijCoreDep()) { includeJars("intellij-core") }
    compileOnly(intellijDep()) { includeIntellijCoreJarDependencies(project) }
    compileOnly(intellijDep("jps-standalone")) { includeJars("jps-model") }
}

sourceSets {
    "main" {
        projectDefault(project)
        resources.srcDir(File(rootDir, "resources")).apply { include("**") }
    }
    "test" {}
}

