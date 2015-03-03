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

--Se um goleiro não está sendo treinado então ele fica aqui
one sig GoleiroSemTreino {
   goleiroSemTreino: set Goleiro
}

--Se um jogador de linha não estiver sem treino então ele é um JogadorSemTreino
one sig JogadorSemTreino {
   jogadorSemTreino: set JogadorDeLinha
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

--****************************************************----------

--Predicados
pred tecnicoAddJogador [tecnico, tecnico': Tecnico, j: JogadorDeLinha] {
	tecnico'.jogadoresDeLinha = tecnico.jogadoresDeLinha + j
}

pred tecnicoRemoveJogador [tecnico, tecnico': Tecnico, j: JogadorDeLinha] {
	tecnico'.jogadoresDeLinha = tecnico.jogadoresDeLinha - j
}

pred preparadorAddJogador [pf, pf': PreparadorFisico, j: JogadorDeLinha] {
	pf'.jogadoresDeLinha = pf.jogadoresDeLinha + j
}

pred preparadorRemoveJogador [pf, pf': PreparadorFisico, j: JogadorDeLinha] {
	pf'.jogadoresDeLinha = pf.jogadoresDeLinha - j
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

// 
pred goleiroTreinando[g: Goleiro]{
	(g in PreparadorFisico.goleiros => g !in TreinadorGoleiro.goleiros)
}


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

---***************************************************************-----
--Fatos

--Maximo de goleiros permitidos é de 3
fact MaximoDeGoleiro {
all g1: Goleiro| g1 not in TreinadorGoleiro.goleiros and g1 not in PreparadorFisico.goleiros => g1 in GoleiroSemTreino.goleiroSemTreino
all g2: Goleiro| g2  in TreinadorGoleiro.goleiros or g2 in PreparadorFisico.goleiros => g2 not in GoleiroSemTreino.goleiroSemTreino
#((TreinadorGoleiro.goleiros + PreparadorFisico.goleiros + GoleiroSemTreino.goleiroSemTreino )) <= 3
}

--Maximo de jogadores de linha permitido é de 10
fact MaximoDeJogadores {
all j1: JogadorDeLinha| j1 not in Tecnico.jogadoresDeLinha and j1 not in PreparadorFisico.jogadoresDeLinha=> j1 in JogadorSemTreino.jogadorSemTreino
all j2: JogadorDeLinha| j2  in Tecnico.jogadoresDeLinha or j2 in PreparadorFisico.jogadoresDeLinha => j2 not in JogadorSemTreino.jogadorSemTreino
#(Tecnico.jogadoresDeLinha + PreparadorFisico.jogadoresDeLinha + JogadorSemTreino.jogadorSemTreino ) <= 10
}

--TreinadorGoleiro não pode treinar o mesmo goleiro do preparador fisico
fact goleiroDiferentes {
  all g: Goleiro| goleiroTreinando[g]
}

// O treinador de goleiro só pode treinar 2 goleiros por vez
fact treinadorDeGoleiro {
   all tg: TreinadorGoleiro| #goleirosDoTreinador[tg] <=2   
}

//Jogadores podem ser treinados ao mesmo tempo pelo técnico e pelo preparador físico
//O preparador físico pode treinar até 5 jogadores
fact preparadorFisico{
   some pf : PreparadorFisico, t : Tecnico, j: JogadorDeLinha | (j in pf.jogadoresDeLinha & t.jogadoresDeLinha)
   all p: PreparadorFisico| #p.jogadoresDeLinha <= 5
}

//O técnico pode treinar até 7 jogadores, mas não pode treinar os mesmos jogadores
fact sobreTecnico {
    all t: Tecnico| #t.jogadoresDeLinha <= 7
}

---****************************************************************-----

--Asserts

// O máximo de jogadores de linha deve ser sete
assert maximoDeGoleiros {
	#((TreinadorGoleiro.goleiros + PreparadorFisico.goleiros + GoleiroSemTreino.goleiroSemTreino )) <= 3
}

// O máximo de goleiros deve ser 3
assert maximoDeJogadores {
	#(Tecnico.jogadoresDeLinha + PreparadorFisico.jogadoresDeLinha + JogadorSemTreino.jogadorSemTreino ) <= 10
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
	all g1: Goleiro| g1 not in TreinadorGoleiro.goleiros and g1 not in PreparadorFisico.goleiros => g1 in GoleiroSemTreino.goleiroSemTreino
	all g2: Goleiro| g2  in TreinadorGoleiro.goleiros or g2 in PreparadorFisico.goleiros => g2 not in GoleiroSemTreino.goleiroSemTreino
}

--check maximoDeGoleiros for 50
--check maximoDeJogadores for 50
--check treinarJogadoresAoMesmoTempo for 50
--check treinadorDeGoleiroDeveTreinarAteDoisGoleirosPorVez for 50
--check treinadorDeGoleiroNaoDeveTreinarOMesmoGoleiroDoTreinadorFisico for 50

pred show[]{}
run show for 10
	
