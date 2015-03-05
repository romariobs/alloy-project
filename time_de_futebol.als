/* Tema 9: Estruturação de um time de futebol

O time de futsal de computação vai representar a UFCG no campeonato regional mas para isso precisa de um
treinamento especíifico, esse time é composto por 3 goleiros e 10 jogadores de linha, o estafe é composto por um técnico,
um preparador físico e um treinador de goleiros. O treinamento dos goleiros é alternado entre o preparador físico e o
treinador de goleiro, nunca juntos, o treinador de goleiros só pode treinar dois goleiros por vez. Os jogadores de linha
podem ser treinados ao mesmo tempo pelo técnico e pelo preparador físico, o preparador físico pode treinar até 5 jogadores
de linha e o técnico pode treinar 7 jogadores, mas não podem treinar os mesmos jogadores.

Integrantes:Romário Batista, Igor Meira, Alan Cintra, Jailson Campos
Cliente: Tiago Massoni

*/

module timeDeFutebol

--Assinaturas
one sig Equipe{
	treinoGoleiro : one TreinoGoleiro,
	treinoJogador : one TreinoJogadoresLinha
}

abstract sig Treino{
	preparadorFisico : one PreparadorFisico
}

one sig TreinoGoleiro extends Treino {
	treinadorGoleiro : one TreinadorGoleiro
}

one sig TreinoJogadoresLinha extends Treino {
	tecnico : one Tecnico
}

one sig Tecnico {
	jogadoresDeLinha : set JogadorDeLinha
}

one sig TreinadorGoleiro {
	goleiros : set Goleiro
}

one sig PreparadorFisico {
	jogadoresDeLinha : set JogadorDeLinha,
	goleiros : set Goleiro
}

sig JogadorDeLinha{}
sig Goleiro{}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Predicados
pred goleiroTreinando[g: Goleiro]{
	(g in PreparadorFisico.goleiros => g not in TreinadorGoleiro.goleiros)
}

//pred goleiroDescansando[g: Goleiro]{
	//(g not in PreparadorFisico.goleiros and g not in TreinadorGoleiro.goleiros => g in Descanso.goleiros )
//}

pred limiteTecnico[t: Tecnico]{
	#t.jogadoresDeLinha <= 7
}

pred limitePreparadorFisico[pf: PreparadorFisico]{
	#pf.jogadoresDeLinha <= 5
}

pred limiteTreinadorGoleiro[tg: TreinadorGoleiro]{
	#tg.goleiros <= 2
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Funcoes
fun goleirosDoTreinador[tg: TreinadorGoleiro] : set Goleiro {
	tg.goleiros
}

fun goleirosDoPreparador[pf: PreparadorFisico] : set Goleiro {
	pf.goleiros
}

fun jogadoresDoPreparador[pf: PreparadorFisico] : set JogadorDeLinha {
	pf.jogadoresDeLinha
}

fun jogadoresDoTecnico[t: Tecnico] : set JogadorDeLinha {
	t.jogadoresDeLinha
}

//////////////////////////////////////////////////////////////////////////////////////////////////
--Fatos
//TreinadorGoleiro não pode treinar o mesmo goleiro do preparador fisico
fact goleiroDiferentes {
	all g: Goleiro| goleiroTreinando[g]
}

// O treinador de goleiro só pode treinar 2 goleiros por vez
fact treinadorDeGoleiro {
   all tg: TreinadorGoleiro | #(tg.goleiros) <= 2
}

//Jogadores podem ser treinados ao mesmo tempo pelo técnico e pelo preparador físico
//O preparador físico pode treinar até 5 jogadores
fact preparadorFisico{
   some pf : PreparadorFisico, t : Tecnico, j: JogadorDeLinha | (j in jogadoresDoPreparador[pf] & jogadoresDoTecnico[t])
   all pf: PreparadorFisico| limitePreparadorFisico[pf]
}

//O técnico pode treinar até 7 jogadores, mas não pode treinar os mesmos jogadores
fact sobreTecnico {
    all t: Tecnico| limiteTecnico[t]
}

//Limite de goleiros = 3
fact limiteGoleiros {
	all tg: TreinadorGoleiro, pf: PreparadorFisico | #(goleirosDoTreinador[tg] + goleirosDoPreparador[pf]) <= 3
}

//Limite de jogadores = 10
fact limiteJogadores{
	all t: Tecnico, pf: PreparadorFisico | #(jogadoresDoPreparador[pf] + jogadoresDoTecnico[t]) <= 12
}

//Todo jogador está com o tecnico ou com o treinador ou com ambos
fact todosJogadoresTreinando{
	all t: Tecnico, pf: PreparadorFisico, j: JogadorDeLinha | (j in jogadoresDoPreparador[pf]) or (j in jogadoresDoTecnico[t])
}

//Todo goleiro está com o preparador ou com o treinador
fact todosGoleirosTreinando{
	all  tg: TreinadorGoleiro, pf: PreparadorFisico, g: Goleiro | (g in goleirosDoPreparador[pf]) or (g in goleirosDoTreinador[tg])
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Asserts

// O máximo de goleiros deve ser 3
assert maximoDeGoleiros {
	#((TreinadorGoleiro.goleiros + PreparadorFisico.goleiros )) <= 3
}

// O máximo de jogadores deve ser 10
assert maximoDeJogadores {
	#(Tecnico.jogadoresDeLinha + PreparadorFisico.jogadoresDeLinha) <= 10
}

// Jogadores podem ser treinados ao mesmo tempo pelo tecnico e pelo preparador fisico
assert treinarJogadoresAoMesmoTempo {
	some t: Tecnico, pf: PreparadorFisico, j : JogadorDeLinha |  (j in pf.jogadoresDeLinha & t.jogadoresDeLinha)
}

// O preparador fisico só pode treinar até 5 jogadores por vez
assert  preparadorFisicoDeveTreinarAteCincoJogadoresPorVez {
	all pf: preparadorFisico | ( #pf.jogadoresDeLinha <= 5 )
}

// O tecnico só pode treinar até 7 jogadores por vez
assert  tecnicoDeveTreinarAteSeteJogadoresPorVez {
	all t: Tecnico | ( #t.jogadoresDeLinha <= 7 )
}

// O treinador de goleiro só pode treinar até dois goleiros por vez
assert  treinadorDeGoleiroDeveTreinarAteDoisGoleirosPorVez {
	all tg: TreinadorGoleiro | ( #tg.goleiros <= 2 )
}

// O Treinador de Goleiro não pode treinar o mesmo goleiro do preparador fisico
assert  treinadorDeGoleiroNaoDeveTreinarOMesmoGoleiroDoTreinadorFisico {
	all g : Goleiro, tg : TreinadorGoleiro, pf : PreparadorFisico | ! ( g in goleirosDoTreinador[tg] and g in goleirosDoPreparador[pf] )
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Checks
--check maximoDeGoleiros for 200
--check maximoDeJogadores for 200
--check treinarJogadoresAoMesmoTempo for 500
check preparadorFisicoDeveTreinarAteCincoJogadoresPorVez for 200
--check tecnicoDeveTreinarAteSeteJogadoresPorVez for 50 // ok
--check treinadorDeGoleiroDeveTreinarAteDoisGoleirosPorVez for 100 // ok
--check treinadorDeGoleiroNaoDeveTreinarOMesmoGoleiroDoTreinadorFisico for 500 // ok

pred show[]{}
run show for 10
	
