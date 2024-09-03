
library(forecast)


# Série temporal com valores em falta e outliers:
plot(gold)

# A função na.interp() identifica os valores em falta e faz a substituição por 
# interpolação linear.
gold1=na.interp(gold)
plot(gold1)

#https://robjhyndman.com/hyndsight/tsoutliers/

