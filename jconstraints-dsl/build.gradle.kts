plugins {
    kotlin("jvm") version "1.5.10"
    id("tools.aqua.jconstraints.java-fatjar-convention")
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints-dsl is the dsl for solver-compositions"

repositories {
    mavenLocal()
    mavenCentral()
}

dependencies {
    implementation(project(":jconstraints-core"))
    implementation(project(":jconstraints-metasolver"))
    implementation(kotlin("stdlib"))
}
