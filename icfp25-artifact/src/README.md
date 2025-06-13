## Project Structure

The files inside the folder have the following chain of dependencies:

```
Syntax.hs <- Behaviour.hs <- HOGSOS.hs <- Separable.hs <- BigStep.hs <- Examples.hs <- Benchmark.hs
```

```                                             
┌───────────┐    ┌──────────────┐    ┌───────────┐    ┌──────────────┐    ┌────────────┐    ┌─────────────┐    ┌───────────────┐
│ Syntax.hs │───►│ Behaviour.hs │───►│ HOGSOS.hs │───►│ Separable.hs │───►│ BigStep.hs │───►│ Examples.hs │───►│ Benchmarks.hs │
└───────────┘    └──────────────┘    └───────────┘    └──────────────┘    └────────────┘    └─────────────┘    └───────────────┘
                                                                                             ┌──────────┐              ▲       
                                                                                             │ Utils.hs │──────────────┘       
                                                                                             └──────────┘                      
```

There is also a file named `Utils.hs` that does not depend on any other file, and only `Benchmark.hs` depends on it.

### File Descriptions

- **Syntax.hs**: Contains the abstract notions needed about the syntax of a language (standard and separated), along with the syntax of xCL and non-deterministic xCL.

- **Behaviour.hs**: Implements the behaviour functor in general (standard and separated), and for the cases of deterministic and non-deterministic behaviour.

- **HOGSOS.hs**: Implements HoGSOS laws in the standard sense, and instantiates xCL as a HoGSOS law.

- **Separable.hs**: Implements separable HoGSOS laws (equipped with multi-step transitions) and instantiates non-deterministic xCL as a separated HoGSOS law.

- **BigStep.hs**: Implements abstract big-step SOS along with its operational model.

- **Examples.hs**: Implements the omega-f-g language from the introduction of the paper, along with three versions of call-by-value xCL.

- **Benchmark.hs**: Contains tests and instructions to run them, showing the results of the small-step (presented by multi-step transition) and big-step specifications.

- **Utils.hs**: Defines an auxiliary function to help with the presentation.

### Adding New Languages

Other languages can easily be tested with the provided code. To do this, define their syntax and behaviour functors as instances of `SepSig` and `SepBeh` respectively. Then, define the separated rules using functions `rhoV` and `rhoC`, and run the desired test cases.


