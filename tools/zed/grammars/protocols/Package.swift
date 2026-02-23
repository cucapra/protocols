// swift-tools-version:5.3
import PackageDescription

let package = Package(
    name: "TreeSitterProtocols",
    products: [
        .library(name: "TreeSitterProtocols", targets: ["TreeSitterProtocols"]),
    ],
    dependencies: [
        .package(url: "https://github.com/ChimeHQ/SwiftTreeSitter", from: "0.8.0"),
    ],
    targets: [
        .target(
            name: "TreeSitterProtocols",
            dependencies: [],
            path: ".",
            sources: [
                "src/parser.c",
                // NOTE: if your language has an external scanner, add it here.
            ],
            resources: [
                .copy("queries")
            ],
            publicHeadersPath: "bindings/swift",
            cSettings: [.headerSearchPath("src")]
        ),
        .testTarget(
            name: "TreeSitterProtocolsTests",
            dependencies: [
                "SwiftTreeSitter",
                "TreeSitterProtocols",
            ],
            path: "bindings/swift/TreeSitterProtocolsTests"
        )
    ],
    cLanguageStandard: .c11
)
