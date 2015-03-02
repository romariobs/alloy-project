/*Tema 9: Estruturação de um time de futebol

O time de futsal de computação vai representar a UFCG no campeonato regional mas para isso precisa de um
treinamento especíifico, esse time é composto por 3 goleiros e 10 jogadores de linha, o estafe é composto por um técnico,
um preparador físico e um treinador de goleiros. O treinamento dos goleiros é alternado entre o preparador físico e o
treinador de goleiro, nunca juntos, o treinador de goleiros só pode treinar dois goleiros por vez. Os jogadores de linha
podem ser treinados ao mesmo tempo pelo técnico e pelo preparador físico, o preparador físico pode treinar até 5 jogadores
de linha e o técnico pode treinar 7 jogadores, mas não podem treinar os mesmos jogadores.

Integrantes:Romário Batista, Igor Meira, Alan Cintra, Jailson Campos
Cliente: Tiago Massoni*/

module timeDeFutebol

--Assinaturas
one sig Equipe{
	treino : set Treino
}

sig JogadorDeLinha extends Equipe{}
sig Goleiro extends Equipe {}

abstract sig Treino{
preparadorFisico : one PreparadorFisico
}

one sig TreinoGoleiro extends Treino {
	treinadorgoleiro : one TreinadorGoleiro
}

one sig TreinoJogadoresLinha extends Treino {
	treinador : one Tecnico
}

one sig Tecnico {
	jogadorDeLinha : set JogadorDeLinha
}

one sig TreinadorGoleiro {
	goleiros : set Goleiro
}

one sig PreparadorFisico {
	jogadorDeLinha : set JogadorDeLinha,
	goleiros : set Goleiro
}

--Predicados
pred tecnicoAddJogador [tecnico, tecnico': Tecnico, j: JogadorDeLinha] {
	tecnico'.jogadorDeLinha = tecnico.jogadordeLinha + j
}

pred tecnicoRemoveJogador [tecnico, tecnico': Tecnico, j: JogadorDeLinha] {
	tecnico'.jogadorDeLinha = tecnico.jogadordeLinha - j
}

pred preparadorAddJogador [pf, pf': PreparadorFisico, j: JogadordeLinha] {
	pf'.jogadorDeLinha = pf.jogadorDeLinha + j
}

pred preparadorRemoveJogador [pf, pf': PreparadorFisico, j: JogadordeLinha] {
	pf'.jogadorDeLinha = pf.jogadorDeLinha - j
}

pred preparadorAddGoleiro [pf, pf': PreparadorFisico, g: Goleiro] {
	pf'.goleiros = pf.goleiros + g
}

pred preparadorRemoveGoleiro [pf, pf': PreparadorFisico, g: Goleiro] {
	pf'.goleiros = pf.goleiros - g
}

pred treinadorAddGoleiro [tg, tg': TreinadorGoleiro, g: Goleiro] {
	tg'.goleiros = tg.goleiros + g
}

pred treinadorRemoveGoleiro [tg, tg': TreinadorGoleiro, g: Goleiro] {
	tg'.goleiros = tg.goleiros - g
}


--Funcoes
fun goleirosDoTreinador[tg: TreinadorGoleiro] : set Goleiro {
  tg.goleiros
}

fun goleirosDoPreparador[pf: PreparadorFisico] : set Goleiro {
  pf.goleiros
}

fun jogadoresDoPreparador[pf: PreparadorFisico] : set JogadorDeLinha {
  pf.jogadorDeLinha
}

fun jogadoresDoTecnico[t: Tecnico] : set JogadorDeLinha {
  t.jogadorDeLinha
}


--Fatos
fact sempre {
//   all g1: Goleiro, g2| g not in TreinadorGoleiro.goleiros and g not in PreparadorFisico.goleiros implies #((TreinadorGoleiro.goleiros + PreparadorFisico.goleiros) + g) = 3
}

// O treinador de goleiro só pode treinar 2 goleiros por vez
fact treinadorDeGoleiro {
   all tg: TreinadorGoleiro| #goleirosDoTreinador[tg] <=2   
}


//Jogadores podem ser treinados ao mesmo tempo pelo técnico e pelo preparador físico
//O preparador físico pode treinar até 5 jogadores
fact preparadorFisico{
   some pf : PreparadorFisico, t : Tecnico | (pf.jogadorDeLinha = t.jogadorDeLinha)
   all p: PreparadorFisico| #p.jogadorDeLinha <= 5
}


//O técnico pode treinar até 7 jogadores, mas não pode treinar os mesmos jogadores
fact sobreTecnico {
    all t: Tecnico| #t.jogadorDeLinha < 7
}


--TreinadorGoleiro não pode treinar o mesmo goleiro do preparador fisico
fact goleiroDiferentes {
  all g: Goleiro| g not in TreinadorGoleiro.goleiros or g not in PreparadorFisico.goleiros
}


--Asserts
//Jogadores podem ser treinados ao mesmo tempo pelo tecnico e pelo preparador fisico
assert treinarJogadoresAoMesmoTempo {
   some t: Tecnico, pF: PreparadorFisico|  t.jogadorDeLinha in pF.jogadorDeLinha
}





--check treinamentoDeGoleirosAlternado for 50
--check treinadorDeGoleirosTreinaDoisGoleirosPorVez
--check treinarJogadoresAoMesmoTempo for 100

pred show[]{}
run tecnicoTemJogador for 10
	
