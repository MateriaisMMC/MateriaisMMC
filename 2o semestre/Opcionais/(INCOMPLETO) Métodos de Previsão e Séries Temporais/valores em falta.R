
library(forecast)


# S�rie temporal com valores em falta e outliers:
plot(gold)

# A fun��o na.interp() identifica os valores em falta e faz a substitui��o por 
# interpola��o linear.
gold1=na.interp(gold)
plot(gold1)

#https://robjhyndman.com/hyndsight/tsoutliers/

