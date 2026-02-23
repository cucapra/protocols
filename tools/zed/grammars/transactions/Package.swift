// swift-tools-version:5.3
import PackageDescription

let package = Package(
    name: "TreeSitterTransactions",
    products: [
        .library(name: "TreeSitterTransactions", targets: ["TreeSitterTransactions"]),
    ],
    dependencies: [
        .package(url: "https://github.com/ChimeHQ/SwiftTreeSitter", from: "0.8.0"),
    ],
    targets: [
        .target(
            name: "TreeSitterTransactions",
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
            name: "TreeSitterTransactionsTests",
            dependencies: [
                "SwiftTreeSitter",
                "TreeSitterTransactions",
            ],
            path: "bindings/swift/TreeSitterTransactionsTests"
        )
    ],
    cLanguageStandard: .c11
)
