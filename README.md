# Chip-Firing with Lean4

A formalization of chip-firing games and the Riemann-Roch theorem for graphs using the Lean 4 theorem prover.

## Overview

This project provides a formal mathematical framework for studying chip-firing games on graphs and proves important results including the Riemann-Roch theorem for graphs. The codebase is structured into several key modules:

- `Basic`: Core definitions and basic utilities
- `CFGraph`: Main chip-firing graph definitions and operations
- `CFGraphExample`: Example graphs and chip-firing scenarios
- `Helpers`: Helper functions and lemmas
- `RRGHelpers`: Helpers specific to Riemann-Roch theorem proofs
- `RiemannRochForGraphs`: Formalization of the Riemann-Roch theorem for graphs

## Requirements

- Lean 4
- Lake build tool
- Required dependencies:
  - `mathlib4`: Mathematical library for Lean 4
  - `Paperproof`: For proof visualization
  - Other dependencies managed via Lake

## Project Structure

```
.
├── ChipFiringWithLean/
│   ├── Basic.lean         
│   ├── CFGraph.lean       # Core chip-firing implementations
│   ├── CFGraphExample.lean # Example graphs and scenarios
│   ├── Helpers.lean       # General helper functions
│   ├── RRGHelpers.lean    # Riemann-Roch specific helpers
│   └── RiemannRochForGraphs.lean # Main theorem proofs
├── lakefile.lean       # Build configuration
└── README.md
```

## Features

- Formal definitions of graphs and chip configurations
- Implementation of chip-firing moves and rules
- Example scenarios with borrowing and lending
- Proofs of key theorems including Riemann-Roch
- Visualization support through Paperproof integration

## Installation

1. Install Lean 4 and Lake following the [official instructions](https://leanprover.github.io/lean4/doc/setup.html)

2. Clone this repository:
```sh
git clone https://github.com/yourusername/chip-firing-with-lean.git
cd chip-firing-with-lean
```

3. Build the project using lake (Lean4 official package manager):
```sh
lake build
```

## Development

The project uses lake for build management. Common commands are as follows:

```sh
lake build        # Build the project
lake clean        # Clean build artifacts
lake exe lean     # Run the Lean executable
```

## License

MIT License

## Contributing

Contributions are welcome! Please feel free to submit pull requests with improvements to proofs, documentation, or new features.

## References

- [Lean4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)