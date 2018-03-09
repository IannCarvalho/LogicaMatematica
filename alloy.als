module controleDeFilmes


---------------------------------------------------------------------------------------------------
--   ASSINATURAS (Mínimo 5, com ao menos 1 herança - extends ou in)
---------------------------------------------------------------------------------------------------


sig Cpf {}

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

sig CurtaMetragem extends Filme {}
sig MediaMetragem extends Filme {}
sig LongaMetragem extends Filme {}


---------------------------------------------------------------------------------------------------
--   FATOS 
---------------------------------------------------------------------------------------------------


fact umCpfPorPessoa {
	all c:Cpf | cpfPorPessoa[c]
}

fact umFilmeUmDiretor {
	all f:Filme | relacaoBidirecionalDeFilmeEDiretor[f]
}


---------------------------------------------------------------------------------------------------
--   PREDICADOS (Mínimo 3) 
---------------------------------------------------------------------------------------------------


--  PREDICADOS PARA FATOS

pred relacaoBidirecionalDeFilmeEDiretor [f : Filme] {
	one f.~filmes and f.~filmes = f.diretor
}

pred cpfPorPessoa [c : Cpf] {
	one c.~cpf
}

--  PREDICADOS PARA ASSERTS

pred umAtorOuMais [f : Filme] {
	#(f.atores) > 0
}

pred numeroDeCpfEhUm [c : Cpf] {
	#(c.~cpf) = 1
}

--------------------------------------------------------------------------------------
--   FUNÇÕES (Mínimo 3) 
--------------------------------------------------------------------------------------


fun filmesDoAtor [c : Cpf] : set Filme {
	atorDoCpf[c].~atores
}

fun atorDoCpf [c : Cpf] : one Ator { 
	c.~cpf & Ator
}

fun filmesDeDiretor [c : Cpf] : set Filme {
	diretorDoCpf[c].filmes
}

fun diretorDoCpf [c : Cpf] : one Diretor {
	c.~cpf & Diretor
}


---------------------------------------------------------------------------------------------------
--   ASSERTS  (Mínimo 3 definições e 3 verificações) 
---------------------------------------------------------------------------------------------------


assert testeFilmeSemAtor {
	all f:Filme | umAtorOuMais[f]
}

check testeFilmeSemAtor for 20

assert testeUmCpfPorPessoa {
	all c : Cpf | numeroDeCpfEhUm[c]
}

check testeUmCpfPorPessoa for 20

assert testeDiretorDoCpf {
	all d : Diretor | d = diretorDoCpf[d.cpf]
}

check testeDiretorDoCpf for 20

assert testeFilmesDeDiretor {
	all d : Diretor | d.filmes = filmesDeDiretor[d.cpf]
}

check testeFilmesDeDiretor for 20


---------------------------------------------------------------------------------------------------
--   SHOW 
---------------------------------------------------------------------------------------------------

pred show[] {}

run show for 8
