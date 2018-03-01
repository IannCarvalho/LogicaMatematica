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

fact umFilmeEmCadaSet{
	all f:Filme | one f.~filmes and f.~filmes = f.diretor
}

--------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
--------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------

fun filmesQueAtorParticipou [c : Cpf] : set Filme {
	(c.~cpf & Ator).~atores
}

fun filmesDeDiretor [c: Cpf] : set Filme {
	diretorDoCpf [c].filmes
}

fun diretorDoCpf [c: Cpf] : one Diretor {
	c.~cpf & Diretor
}

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

assert testeDiretorDoCpf {
	all d:Diretor | d = diretorDoCpf[d.cpf]
}

check testeDiretorDoCpf

assert testeFilmesDeDiretor{
	all d:Diretor | d.filmes = filmesDeDiretor[d.cpf]
}
check testeFilmesDeDiretor


--------------------------------------------------------------------------------------
--   SHOW 
--------------------------------------------------------------------------------------

pred show[]{#Ator > 3
}

run show
