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

//Assinaturas
one sig Time {
	treinos : set Treino
}

abstract sig Treino{}

one sig TreinoGoleiro extends Treino {
	treinadorgoleiro : one TreinadorGoleiro,
	preparadorfisico : lone PreparadorFisico
}

one sig TreinoJogadoresLinha extends Treino {
	treinador : one Tecnico,
	preparadorfisico : lone PreparadorFisico
}

one sig Tecnico {
	jogadoresDeLinha : set JogadorLinha,
}

one sig TreinadorGoleiro {
	goleiros : set Goleiro,
}

one sig PreparadorFisico {
	jogadoresDeLinha : set JogadorLinha,
	goleiros : set Goleiro
}

sig Goleiro{}
sig JogadorLinha{}


//Fatos 
// O treinador de goleiro só pode treinar 2 goleiros por vez
fact treinadorDeGoleiro {
   all t: TreinadorGoleiro| #t.goleiros <=2
   
}



//Jogadores podem ser treinados ao mesmo pelo técnico e pelo preparador físico
//O preparador físico pode treinar até 5 jogadores
fact preparadorFisico{
   some pf : PreparadorFisico, t : Tecnico | (pf.jogadoresDeLinha = t.jogadoresDeLinha)
   all p: PreparadorFisico| #p.jogadoresDeLinha <= 5
}


//O técnico pode treinar até 7 jogadores, mas não pode treinar os mesmos jogadores
fact sobreTecnico {
    all t: Tecnico| #t.jogadoresDeLinha < 7
}

//Asserts
assert treinamentoDeGoleirosAlternado {
	one p:PreparadorFisico | one t:TreinadorGoleiro| some p.goleiros or #t.goleiros = 2
}

assert treinadorDeGoleirosTreinaDoisGoleirosPorVez {
	one t:TreinadorGoleiro | #t.goleiros = 2
}

assert treinadorEPreparadorPodemTreinarJogadoresAoMesmoTempo {
	one t:Tecnico | one p:PreparadorFisico | no t.jogadoresDeLinha & p.jogadoresDeLinha
}

//check treinamentoDeGoleiros
//check treinadorDeGoleirosTreinaDoisGoleirosPorVez
//check treinadorEPreparadorPodemTreinarJogadoresAoMesmoTempo

pred show[]{}
run show for 20
	
