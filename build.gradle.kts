plugins {
    `java-library`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.johnrengelman.shadow") version "5.2.0"
}

repositories {
    jcenter()
    mavenLocal()
    mavenCentral()
}

dependencies {

    implementation("tools.aqua:jconstraints-all:0.9.6-SNAPSHOT")
    implementation("solver:CVC4-gpl:1.8.0")
    implementation("org.apache.commons:commons-math3:3.6.1")

    testImplementation("org.testng:testng:7.0.0")
}

val test by tasks.getting(Test::class) {
    // Use TestNG for unit tests
    useTestNG()
}

tasks.shadowJar {
    //FIXME: Exclude the other jconstraints-deps
    exclude("tools.aqua:jconstraints-all:.*")

}

license {
    header = rootProject.file("NOTICE")
    strictCheck = true
}
