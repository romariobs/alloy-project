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
abstract sig Equipe{}

sig JogadorDeLinha extends Equipe {}
sig Goleiro extends Equipe{}

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
	jogadoresDeLinha : set JogadorDeLinha
}

one sig TreinadorGoleiro {
	goleiros : set Goleiro
}

one sig PreparadorFisico {
	jogadoresDeLinha : set JogadorDeLinha,
	goleiros : set Goleiro
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Predicados
pred goleiroTreinando[g: Goleiro]{
	(g in PreparadorFisico.goleiros => g !in TreinadorGoleiro.goleiros)
}

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

--TreinadorGoleiro não pode treinar o mesmo goleiro do preparador fisico
fact goleiroDiferentes {
	all g: Goleiro| goleiroTreinando[g]
}

// O treinador de goleiro só pode treinar 2 goleiros por vez
fact treinadorDeGoleiro {
   all tg: TreinadorGoleiro| limiteTreinadorGoleiro[tg] 
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
	some tg: TreinadorGoleiro, pf: PreparadorFisico | #(pf.goleiros+tg.goleiros) <= 3
}

//Limite de jogadores = 10
fact limiteJogadores{
	some t: Tecnico, pf: PreparadorFisico, j: JogadorDeLinha | j !in (jogadoresDoPreparador[pf] + jogadoresDoTecnico[t]) => #(jogadoresDoPreparador[pf] + jogadoresDoTecnico[t]) <= 10
}

//Todo jogador está com o tecnico ou com o treinador ou com ambos
fact todosGoleirosTreinando{
	all t: Tecnico, pf: PreparadorFisico, j: JogadorDeLinha | (j in jogadoresDoPreparador[pf]) or (j in jogadoresDoTecnico[t])
}

//Todo goleiro está com o preparador ou com o treinador
fact todosGoleirosTreinando{
	some tg: TreinadorGoleiro, pf: PreparadorFisico, g: Goleiro | (g in goleirosDoPreparador[pf]) => (g !in goleirosDoTreinador[tg])
    some tg: TreinadorGoleiro, pf: PreparadorFisico, g: Goleiro | (g in goleirosDoTreinador[tg]) => (g !in goleirosDoPreparador[pf])
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Asserts

// O máximo de jogadores de linha deve ser sete
assert maximoDeGoleiros {
	#((TreinadorGoleiro.goleiros + PreparadorFisico.goleiros )) <= 3
}

// O máximo de goleiros deve ser 3
assert maximoDeJogadores {
	#(Tecnico.jogadoresDeLinha + PreparadorFisico.jogadoresDeLinha) <= 10
}

// Jogadores podem ser treinados ao mesmo tempo pelo tecnico e pelo preparador fisico
assert treinarJogadoresAoMesmoTempo {
	some t: Tecnico, pF: PreparadorFisico, jo : JogadorDeLinha |  (jo in pF.jogadoresDeLinha & t.jogadoresDeLinha)
}

// O treinador de goleiro só pode treinar até dois goleiros por vez
assert  treinadorDeGoleiroDeveTreinarAteDoisGoleirosPorVez {
	all tg: TreinadorGoleiro| ( #tg.goleiros <= 2 )
}

// O Treinador de Goleiro não pode treinar o mesmo goleiro do preparador fisico
assert  treinadorDeGoleiroNaoDeveTreinarOMesmoGoleiroDoTreinadorFisico {
	all goleiros : Goleiro, tg : TreinadorGoleiro, pf : PreparadorFisico | (goleiros not in goleirosDoTreinador[tg]) or (goleiros not in goleirosDoPreparador[pf])
}

//////////////////////////////////////////////////////////////////////////////////////////////////

--Checks
--check maximoDeGoleiros for 50
--check maximoDeJogadores for 50
--check treinarJogadoresAoMesmoTempo for 50
--check treinadorDeGoleiroDeveTreinarAteDoisGoleirosPorVez for 50
--check treinadorDeGoleiroNaoDeveTreinarOMesmoGoleiroDoTreinadorFisico for 50

pred show[]{}
run show for 10
	
