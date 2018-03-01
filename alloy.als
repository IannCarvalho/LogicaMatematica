module controleDeFilmes
--------------------------------------------------------------------------------------
--   ASSINATURAS (Mínimo 5, com ao menos 1 herança - extends ou in)
--------------------------------------------------------------------------------------

sig Cpf{}

abstract sig Pessoa {
	cpf: one Cpf
}

sig Diretor extends Pessoa {
	filmes: set Filme
}

sig Ator extends Pessoa {}

abstract sig Filme {
	diretor: one Diretor,
	atores: some Ator
}

sig CurtaMetragem extends Filme{}
sig MediaMetragem extends Filme{}
sig LongaMetragem extends Filme{}

--------------------------------------------------------------------------------------
--   FATOS 
--------------------------------------------------------------------------------------

fact umCpfPorPessoa{
	all c:Cpf | one c.~cpf
}

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
--------------------------------------------------------------------------------------

assert testeFilmeSemAtor{
	all f:Filme | #(f.atores) > 0
}

check testeFilmeSemAtor

assert testeUmCpfPorPessoa{
	all c:Cpf | #(c.~cpf) = 1
}

check testeUmCpfPorPessoa

--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{}

run show
