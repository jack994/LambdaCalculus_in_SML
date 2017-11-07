# Lambda Calculus in SML

The program implements beta and eta reduction in SML as well as the translations to different notations of lambda calculus and Combinatory Logic.

The syntax of λ-calculus is given by  M ::= V | (λV.M) | (MM)

The syntax of λ-calculus in item notation is given by  M′ ::= V | [V] M′ |〈M′〉M′

The syntax of λ-calculus with de Bruijn indices is given by  Λ  ::= N | (λΛ) | (ΛΛ)

The syntax of λ-calculus in item notation is given by Λ′ ::= N | [ ] Λ′ |〈Λ′〉Λ′

The syntax of combinatory logic is given by M′′ ::= V | I′′ | K′′ | S′′ | (M′′M′′)
