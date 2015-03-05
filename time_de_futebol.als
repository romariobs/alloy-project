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
	treinogoleiro : one TreinoGoleiro,
	treinojogador : one TreinoJogadoresLinha
}

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
	jogadoresT : set JogadorDeLinha
}

one sig TreinadorGoleiro {
	goleirosTg : set Goleiro
}

one sig PreparadorFisico {
	jogadoresPf : set JogadorDeLinha,
	goleirosPf : set Goleiro
}

one sig Chuveiro {
   jogadoresC: set JogadorDeLinha,
   goleirosC: set Goleiro
}

sig JogadorDeLinha{}
sig Goleiro{}

////////////////////////////////////////////.....FUNÇÕES....//////////////////////////////////////////////////

fun goleirosNoChuveiro[c: Chuveiro]: set Goleiro {
   c.goleirosC
}

fun goleirosDoTreinador[tr: TreinadorGoleiro]: set Goleiro {
   tr.goleirosTg
}

fun goleirosDoPreparador[p: PreparadorFisico] : set Goleiro {
   p.goleirosPf
}

fun jogadoresNoChuveiro[c: Chuveiro] : set JogadorDeLinha {
   c.jogadoresC
}

fun jogadoresDoTecnico[t: Tecnico] : set JogadorDeLinha {
   t.jogadoresT
}

fun jogadoresDoPreparador[p: PreparadorFisico] : set JogadorDeLinha {
   p.jogadoresPf
}

fun todosOsGoleiros[tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro] : set Goleiro {
  goleirosDoTreinador[tg] + goleirosDoPreparador[pf] + goleirosNoChuveiro[c]
}

fun todosOsJogadores[pf: PreparadorFisico, t: Tecnico, c: Chuveiro] : set JogadorDeLinha {
  jogadoresDoPreparador[pf] +  jogadoresDoTecnico[t] + jogadoresNoChuveiro[c]
}

///////////////////////////////////////////////.....FATOS......///////////////////////////////////////////////

fact sobreTreinoGoleiro {
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in goleirosDoTreinador[tg] => (#goleirosDoPreparador[pf] = 0)
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in goleirosDoPreparador[pf] => (#goleirosDoTreinador[tg]= 0)

  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| goleiroSemTreino[g, pf, tg] => goleiroNoChuveiro[g, c]

  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| !goleiroSemTreino[g, pf, tg] => goleiroNoChuveiro[g, c]

  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| goleiroNoChuveiro[g, c] => goleiroSemTreino[g, pf, tg]

  all tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| #todosOsGoleiros[tg, pf, c] = 3

  all tg: TreinadorGoleiro| #goleirosDoTreinador[tg] <= 2
}

fact sobreTreinoJogador {
  all pf: PreparadorFisico| #jogadoresDoPreparador[pf] <= 5
  all t: Tecnico| #jogadoresDoTecnico[t] <= 7
  all pf: PreparadorFisico, t: Tecnico, c: Chuveiro| #todosOsJogadores[pf, t, c] = 10
  
  all j: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico| jogadorTreinaComPreparador[j, pf] => !jogadorTreinaComTecnico[j, t]
  all j: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico| jogadorTreinaComTecnico[j, t] => !jogadorTreinaComPreparador[j, pf]
  all j: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico, c: Chuveiro| jogadorSemTreino[j, pf, t] => jogadorNoChuveiro[j, c]
  all j: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico, c: Chuveiro| !jogadorSemTreino[j, pf, t] => !jogadorNoChuveiro[j, c]

}

////////////////////////////////////////////.....PREDICADOS....//////////////////////////////////////////////

pred jogadorSemTreino[j: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico] {
  j !in jogadoresDoTecnico[t] and j !in jogadoresDoPreparador[pf]
}

pred goleiroSemTreino[g: Goleiro, pf: PreparadorFisico, tg: TreinadorGoleiro] {
  (g !in goleirosDoPreparador[pf]) and (g !in goleirosDoTreinador[tg])
}

pred jogadorTreinaComPreparador[j: JogadorDeLinha, pf: PreparadorFisico] {
  j in jogadoresDoPreparador[pf]
}

pred jogadorTreinaComTecnico[j: JogadorDeLinha, t: Tecnico] {
  j in jogadoresDoTecnico[t]
}

pred jogadorNoChuveiro[j: JogadorDeLinha, c: Chuveiro] {
  j in jogadoresNoChuveiro[c]
}

pred goleiroNoChuveiro[g: Goleiro, c: Chuveiro] {
  g in goleirosNoChuveiro[c]
}

pred goleiroTreinaComPreparador[g: Goleiro, pf: PreparadorFisico] {
  g in goleirosDoPreparador[pf]
}

pred goleiroTreinaComTreinador[g: Goleiro, tg: TreinadorGoleiro] {
  g in goleirosDoTreinador[tg]
}

////////////////////////////////////////////......ASSERTS....//////////////////////////////////////////////////

assert apenasUmaEquipe {
   one Equipe
}

assert todoGoleiro {
  all g1, g2: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico|(g1 != g2) and goleiroTreinaComTreinador[g1, tg] => (!goleiroTreinaComPreparador[g2, pf])
  all g1, g2: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico|(g1 != g2) and goleiroTreinaComPreparador[g1, pf] => (!goleiroTreinaComTreinador[g2, tg])
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| goleiroTreinaComTreinador[g, tg] => (#goleirosDoPreparador[pf]  = 0)
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| goleiroTreinaComPreparador[g, pf]  => (#goleirosDoTreinador[tg] = 0)
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| goleiroNoChuveiro[g, c] => goleiroSemTreino[g, pf, tg]
  lone t: TreinadorGoleiro| #goleirosDoTreinador[t] = 2
}

assert todoJogador {
  lone t: Tecnico| #jogadoresDoTecnico[t] = 7
  lone pf: PreparadorFisico| #jogadoresDoPreparador[pf] = 5
  lone c: Chuveiro| #jogadoresNoChuveiro[c] = 10
  some j1, j2: JogadorDeLinha, pf: PreparadorFisico, t: Tecnico| j1 != j2 => jogadorTreinaComPreparador[j1, pf] and jogadorTreinaComTecnico[j2, t]
}

//check apenasUmaEquipe for 200
check todoGoleiro for 200
//check todoJogador for 200

pred show[]{}
run show for 10
	
