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
	jogadoresDeLinha : set JogadorDeLinha
}

one sig TreinadorGoleiro {
	goleiros : set Goleiro
}

one sig PreparadorFisico {
	jogadoresDeLinha : set JogadorDeLinha,
	goleiros : set Goleiro
}

one sig Chuveiro {
   jogadores: set JogadorDeLinha,
   goleiros: set Goleiro
}

sig JogadorDeLinha{}
sig Goleiro{}

//////////////////////////////////////////////////////////////////////////////////////////////////

fact sobreTreinoGoleiro {
   all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in tg.goleiros => (#pf.goleiros = 0)
   all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in pf.goleiros => (#tg.goleiros = 0)

   all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| ((g !in pf.goleiros) and (g !in tg.goleiros)) => g in c.goleiros
   all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| ((g in pf.goleiros) or (g in tg.goleiros)) => g !in c.goleiros

    all tg: TreinadorGoleiro, pf: PreparadorFisico, c: Chuveiro| #(tg.goleiros + pf.goleiros+c.goleiros) = 3
    all tg: TreinadorGoleiro| #tg.goleiros <= 2
}


//////////////////////////////////////////////////////////////////////////////////////////////////

assert todoGoleiro {
  all g1, g2: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico|(g1 != g2) and g1 in tg.goleiros => (g2 !in pf.goleiros)
  all g1, g2: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico|(g1 != g2) and g1 in pf.goleiros => (g2 !in tg.goleiros)
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in tg.goleiros => (#pf.goleiros = 0)
  all g: Goleiro, tg: TreinadorGoleiro, pf: PreparadorFisico| g in pf.goleiros => (#tg.goleiros = 0)
  lone t: TreinadorGoleiro| #t.goleiros = 2
}

check todoGoleiro for 50

pred show[]{}
run show for 10
	
