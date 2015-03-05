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

open util/ordering[Time] as to
sig Time{}

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
	jogadoresT : JogadorDeLinha -> Time
}

one sig TreinadorGoleiro {
	goleirosTg : Goleiro -> Time
}

one sig PreparadorFisico {
	jogadoresPf : JogadorDeLinha -> Time,
	goleirosPf : Goleiro -> Time
}

one sig Chuveiro {
   jogadoresC: JogadorDeLinha -> Time,
   goleirosC: Goleiro -> Time
}

sig JogadorDeLinha{}
sig Goleiro{}

////////////////////////////////////////////.....FUNÇÕES....//////////////////////////////////////////////////

fun goleirosNoChuveiro[c: Chuveiro, t:Time]: set Goleiro {
   (c.goleirosC).t
}

fun goleirosDoTreinador[tr: TreinadorGoleiro, t:Time]: set Goleiro {
   (tr.goleirosTg).t
}

fun goleirosDoPreparador[p: PreparadorFisico, t:Time] : set Goleiro {
   (p.goleirosPf).t
}

fun jogadoresNoChuveiro[c: Chuveiro, t:Time] : set JogadorDeLinha {
   (c.jogadoresC).t
}

fun jogadoresDoTecnico[tc: Tecnico, t:Time] : set JogadorDeLinha {
   (tc.jogadoresT).t
}

fun jogadoresDoPreparador[p: PreparadorFisico, t:Time] : set JogadorDeLinha {
   (p.jogadoresPf).t
}

fun todosOsGoleiros[tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time] : set Goleiro {
  goleirosDoTreinador[tg, t] + goleirosDoPreparador[pf, t] + goleirosNoChuveiro[c, t]
}

fun todosOsJogadores[pf: PreparadorFisico, tc: Tecnico, c: Chuveiro, t:Time] : set JogadorDeLinha {
  jogadoresDoPreparador[pf, t] +  jogadoresDoTecnico[tc, t] + jogadoresNoChuveiro[c, t]
}

///////////////////////////////////////////////.....FATOS......///////////////////////////////////////////////

fact sobreTreinoGoleiro {

  // se um goleiro está com o treinador de goleiros nao deve estar com o preparador fisico
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, t:Time | g in goleirosDoTreinador[tg, t] => g not in goleirosDoPreparador[pf, t]

  // se um goleiro está com o preparador fisico nao deve estar com o treinador de goleiros
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, t:Time | g in goleirosDoPreparador[pf, t] => g not in goleirosDoTreinador[tg, t]

  // goleiro sem treino é goleiro no chuveiro
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time | goleiroSemTreino[g, pf, tg, t] => goleiroNoChuveiro[g, c, t]

  // goleiro no chuveiro é goleiro sem treino
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time | goleiroNoChuveiro[g, c, t] => goleiroSemTreino[g, pf, tg, t]

  // se o goleiro está treinando não pode estar no chuveiro
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time | !goleiroSemTreino[g, pf, tg, t] => !goleiroNoChuveiro[g, c, t]

  // maximo de goleiros = 3
  all tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time | #todosOsGoleiros[tg, pf, c, t] = 3

  // maximo de goleiros que o treinador de goleiros pode treinar = 2 
  all tg: TreinadorGoleiro, t:Time | #goleirosDoTreinador[tg, t] <= 2

}

fact sobreTreinoJogador {

  // maximo de jogadores que o preparador fisico pode treinar = 5 
  all pf: PreparadorFisico, t:Time | #jogadoresDoPreparador[pf, t] <= 5

  // maximo de jogadores que o tecnico pode treinar = 7 
  all tc: Tecnico, t:Time | #jogadoresDoTecnico[tc, t] <= 7

  // maximo de jogadores do time = 10
  all pf: PreparadorFisico, tc: Tecnico, c: Chuveiro, t:Time | #todosOsJogadores[pf, tc, c, t] = 10

  // jogador que treina com tecnico não treina com preparador físico e vice-versa
  all j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, t:Time | jogadorTreinaComPreparador[j, pf, t] => !jogadorTreinaComTecnico[j, tc, t]
  all j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, t:Time | jogadorTreinaComTecnico[j, tc, t] => !jogadorTreinaComPreparador[j, pf, t]
  
  // jogador sem treino é jogador no chuveiro
  all j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, c: Chuveiro, t:Time | jogadorSemTreino[j, pf, tc, t] => jogadorNoChuveiro[j, c, t]

  // se o jogador está treinando não pode estar no chuveiro
  all j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, c: Chuveiro, t:Time | !jogadorSemTreino[j, pf, tc, t] => !jogadorNoChuveiro[j, c, t]

  // jogador no chuveiro é jogador sem treino
  all j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, c: Chuveiro, t:Time | jogadorNoChuveiro[j, c, t] => jogadorSemTreino[j, pf, tc, t]

}

fact traces {
	initT [first]
	all pre: Time-last | let pos = pre.next |
		some tc: Tecnico, j: JogadorDeLinha |
			addJogadorT[tc,j,pre,pos] or
			removeJogadorT[tc,j,pre,pos]

	initPFJ [first]
	all pre: Time-last | let pos = pre.next |
		some pf: PreparadorFisico, j: JogadorDeLinha |
			addJogadorPF[pf,j,pre,pos] or
			removeJogadorPF[pf,j,pre,pos]

	initPFG [first]
	all pre: Time-last | let pos = pre.next |
		some pf: PreparadorFisico, tg:TreinadorGoleiro, g: Goleiro |
			addGoleiroPF[pf,tg,g,pre,pos] or
			removeGoleiroPF[pf,g,pre,pos]

	initTG [first]
	all pre: Time-last | let pos = pre.next |
		some tg:TreinadorGoleiro, pf:PreparadorFisico, g: Goleiro |
			addGoleiroTG[tg,pf,g,pre,pos] or
			removeGoleiroTG[tg,g,pre,pos]
}

////////////////////////////////////////////.....PREDICADOS....//////////////////////////////////////////////

pred jogadorSemTreino[j: JogadorDeLinha, pf: PreparadorFisico, tc: Tecnico, t:Time] {
  j !in jogadoresDoTecnico[tc, t] and j !in jogadoresDoPreparador[pf, t]
}

pred goleiroSemTreino[g: Goleiro, pf: PreparadorFisico, tg: TreinadorGoleiro, t:Time] {
  (g !in goleirosDoPreparador[pf, t]) and (g !in goleirosDoTreinador[tg, t])
}

pred jogadorTreinaComPreparador[j: JogadorDeLinha, pf: PreparadorFisico, t:Time] {
  j in jogadoresDoPreparador[pf, t]
}

pred jogadorTreinaComTecnico[j: JogadorDeLinha, tc: Tecnico, t:Time] {
  j in jogadoresDoTecnico[tc, t]
}

pred jogadorNoChuveiro[j: JogadorDeLinha, c: Chuveiro, t:Time] {
  j in jogadoresNoChuveiro[c, t]
}

pred goleiroNoChuveiro[g: Goleiro, c: Chuveiro, t: Time] {
  g in goleirosNoChuveiro[c, t]
}

pred goleiroTreinaComPreparador[g: Goleiro, pf: PreparadorFisico, t:Time] {
  g in goleirosDoPreparador[pf, t]
}

pred goleiroTreinaComTreinador[g: Goleiro, tg: TreinadorGoleiro, t:Time] {
  g in goleirosDoTreinador[tg, t]
}

pred initT [t: Time] {
	no (Tecnico.jogadoresT).t
}

pred initPFJ [t: Time] {
	no (PreparadorFisico.jogadoresPf).t
}

pred initPFG [t: Time] {
	no (PreparadorFisico.goleirosPf).t
}

pred initTG [t: Time] {
	no (TreinadorGoleiro.goleirosTg).t
}

pred addJogadorT[tc:Tecnico, j:JogadorDeLinha, t, t':Time] {
	j !in (tc.jogadoresT).t
	(tc.jogadoresT).t' = (tc.jogadoresT).t + j
}

pred addJogadorPF[pf:PreparadorFisico, j:JogadorDeLinha, t, t':Time] {
	j !in (pf.jogadoresPf).t
	(pf.jogadoresPf).t' = (pf.jogadoresPf).t + j
}


pred removeJogadorT[tc:Tecnico, j:JogadorDeLinha, t, t':Time] {
	j in (tc.jogadoresT).t
	(tc.jogadoresT).t' = (tc.jogadoresT).t - j
}

pred removeJogadorPF[pf:PreparadorFisico, j:JogadorDeLinha, t, t':Time] {
	j in (pf.jogadoresPf).t
	(pf.jogadoresPf).t' = (pf.jogadoresPf).t - j
}

// se remover 'and #pf.goleirosPf <=2 and #tg.goleirosTg = 0' o programa consegue achar uma instância
pred addGoleiroPF[pf:PreparadorFisico, tg:TreinadorGoleiro, g:Goleiro, t, t':Time] {
	g !in (pf.goleirosPf).t and #pf.goleirosPf <=2 and #tg.goleirosTg = 0
	(pf.goleirosPf).t' = (pf.goleirosPf).t + g
}

// mesmo caso do predicado acima
pred addGoleiroTG[tg:TreinadorGoleiro, pf:PreparadorFisico, g:Goleiro, t, t':Time] {
	g !in (tg.goleirosTg).t and #tg.goleirosTg <=1 and #pf.goleirosPf = 0
	(tg.goleirosTg).t' = (tg.goleirosTg).t + g
}


pred removeGoleiroPF[pf:PreparadorFisico, g:Goleiro, t, t':Time] {
	g in (pf.goleirosPf).t
	(pf.goleirosPf).t' = (pf.goleirosPf).t - g
}

pred removeGoleiroTG[tg:TreinadorGoleiro, g:Goleiro, t, t':Time] {
	g in (tg.goleirosTg).t
	(tg.goleirosTg).t' = (tg.goleirosTg).t - g
}



////////////////////////////////////////////......ASSERTS....//////////////////////////////////////////////////

assert apenasUm {
  one Equipe
  one TreinadorGoleiro
  one PreparadorFisico
  one Tecnico
}

assert todoGoleiro {
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, t:Time | goleiroTreinaComTreinador[g, tg, t] => (!goleiroTreinaComPreparador[g, pf, t])
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, t:Time | goleiroTreinaComPreparador[g, pf, t] => ( !goleiroTreinaComTreinador[g, tg, t])
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time| goleiroNoChuveiro[g, c, t] => goleiroSemTreino[g, pf, tg, t]
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time| goleiroSemTreino[g, pf, tg, t] => goleiroNoChuveiro[g, c, t]
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time| !goleiroSemTreino[g, pf, tg, t] => !goleiroNoChuveiro[g, c, t]
  all tg: TreinadorGoleiro, t:Time| #goleirosDoTreinador[tg, t] <= 2
  all tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro, t:Time | #todosOsGoleiros[tg, pf, c, t] = 3
}

assert todoJogador {
  all j: JogadorDeLinha, tc: Tecnico, pf: PreparadorFisico, t:Time | jogadorTreinaComPreparador[j, pf, t]  => (!jogadorTreinaComTecnico[j, tc, t])
  all j: JogadorDeLinha, tc: Tecnico, pf: PreparadorFisico, t:Time | jogadorTreinaComTecnico[j, tc, t] => ( !jogadorTreinaComPreparador[j, pf, t])
  all j: JogadorDeLinha, tc: Tecnico, pf: PreparadorFisico, c: Chuveiro, t:Time | jogadorNoChuveiro[j, c, t] => jogadorSemTreino[j, pf, tc, t]
  all j: JogadorDeLinha, tc: Tecnico, pf: PreparadorFisico, c: Chuveiro, t:Time | jogadorSemTreino[j, pf, tc, t] => jogadorNoChuveiro[j, c, t]
  all j: JogadorDeLinha, tc: Tecnico, pf: PreparadorFisico, c: Chuveiro, t:Time | !jogadorSemTreino[j, pf, tc, t] => !jogadorNoChuveiro[j, c, t]
  all tc: Tecnico, t:Time | #jogadoresDoTecnico[tc, t] <= 7
  all pf: PreparadorFisico, t:Time | #jogadoresDoPreparador[pf, t] <= 5
  all c: Chuveiro, t:Time | #jogadoresNoChuveiro[c, t] <= 10
}

//check apenasUm for 200
//check todoGoleiro for 200
//check todoJogador for 200

pred show[]{}
run show for 10
	
