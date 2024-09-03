library(faraway)
data(savings)
modelo=lm(sr~.,data=savings)

step(modelo)

step(modelo,direction="backward")

step(modelo,direction="both")

modelonulo=lm(sr~1,data=savings)
step(modelonulo,direction="forward",scope=list(lower=modelonulo,upper=modelo))

drop1(modelo,test="F")

modelo1=lm(sr~.-dpi,data=savings)
drop1(modelo1,test="F")

modelo2=lm(sr~.-dpi-pop75,data=savings)
drop1(modelo2,test="F")


add1(modelonulo,modelo,test="F")

modelo1=lm(sr~pop15,data=savings)


add1(modelo1,modelo,test="F")

modelo2=lm(sr~pop15+ddpi,data=savings)


add1(modelo2,modelo,test="F")

