I###########################
# Data sets related to the 50 states of the United States of America.
########################### 
state <- data.frame(state.x77)
names(state)
dim(state)

# O objectivo Ž seleccionar o melhor modelo utilizando a metodologia backward selection, ou seja, step-down.
# Para isso, comeamos por ajustar o modelo contendo todas as vari‡veis.

modelo1<-lm(Life.Exp~., data=state)
summary(modelo1)

step(modelo1, direction=c("backward"))

modelo0=lm(Life.Exp~1,data=state)
extractAIC(modelo1)
extractAIC(modelo0)

step(modelo0, Life.Exp~Population + Income + Illiteracy + Murder + HS.Grad + Frost +
        Area, direction="forward", data=state)


# MODELO SELECCIONADO
# Y = beta0 + beta1*Murder + beta2*HS.Grad + beta3*Frost + beta4*Population + epsilon