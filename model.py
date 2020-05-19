import matplotlib.pyplot as plt
import numpy as np
import matplotlib as mpl
import matplotlib.dates as mdates
import datetime as dt
import csv
import matplotlib.animation
from matplotlib import cm
from scipy.io import loadmat
import pandas as pd
import sys
import tqdm
from tqdm import tqdm_notebook
import pickle
import _pickle
import cvxpy
import random
import math
import copy
from IPython.html import widgets
from IPython.display import display,clear_output
from mpl_toolkits.mplot3d import Axes3D
import warnings
warnings.filterwarnings('ignore')
import time





%matplotlib notebook
%matplotlib notebook


class Territory:
    def __init__(self, name, row, column, resources, sphere = True, radius = 900.1, percent = False):  # объявление территории(Название, высота, ширина, кол-во ресурсов, есть ли искревление, радиус искревления)
        #массив участков ([ресурсы,], root or eez?, страна+1, [дистанции], [польза], eez?)
        self.unos = [[[[0] * resources, False, -1, [], [], False] for i in range(column)] for i in range(row)]
        self.countries = []      # массив стран (приоритеты, удовлетворение, корни, территоии, eez)
        self.name = name         # название территории
        self.names = []          # название стран
        self.ind = []            # массив индикаторов стран нужный для charity и fun_balance
        self.d = []              # границы полезности
        self.change_map = []     # массив изменения карты для анимации
        self.change_sati = []     # массив изменени удовлетворений стран для гистограммы c 0 по последнюю итерацию
        self.start_map = []      # первый вариант карты
        self.start_map_diff = [] # первый вариант карты с расширенной расцветкой
        self.res_map = np.zeros((resources, row, column))  # карты ресурсов
        self.dist_map = []       # карты расстояний
        self.sati_map = []       # карты полезностей
        self.transferable = []   # массив реальных элементов которые можно передавать
        self.i_char = 0          # счётчик количества передачи участков из-за charity
        self.i_exch = 0          # счётчик количества передачи участков из-за exchange
        self.i_exch2 = 0         # счётчик количества обменов в exchange
        self.isave = 0           # индикатор сохранения карты
        self.sphere = sphere     # есть ли искривление поверхности?
        self.radius = radius     # радиус искривления
        self.z = []              # третья координата(от северного полюса)
        self.inline = 0          # счётчик inline для matplotlib
        self.angle1 = 30         # угол для 3д отображения
        self.angle2 = 30         # второй угол для 3д отбражения
        self.list_exchange = []  # сосед из страны i стране j который может ей уйти
        self.map_exchange = []   # карта соседей каждого участка
        self.started = []        # массив участков стран для промежуточного вычесления расстояний
        self.exchanged = [{}, {}, {}] # словари с информацией о статистике обмена ункцией exchange
        self.percent = percent   # является ли модель процентной
        self.full = []           # для процентной модели, чему равны 100% уровня удовлетворённости стран
        if self.sphere:          # заполнение self.z
            for i in range(row):
                self.z.append([])
                for j in range(column): # расчёт третьей координаты с учётом искривления 
                    self.z[i].append(self.radius - pow(pow(self.radius, 2) - ((pow(i - row/2 + 0.5, 2) + pow(j - column/2 + 0.5,2))), 0.5))
        else:
            for i in range(row):
                self.z.append([])
                for j in range(column):
                    self.z[i].append(0)

            
        ### ПОЛЬЗОВАТЕЛЬСКИЕ ФУНКЦИИ ###
        
        
        
      ## РЕДАКТИРОВАНИЕ КАРТЫ ## 
        
        
    # ДОБАВЛЕНИЕ СТРАНЫ (название, приоритеты, границы пользы)
    def add_country(self, name, priorities, dis):
        self.countries.append([priorities, 0, [], [], []]) # приоритеты удовлетворение корни территоии, eez
        self.ind.append(0)                       # добавление индикатора
        self.full.append(0)
        self.names.append(name)                  # добавление имени
        self.d.append(dis)                       # добавление границ пользы
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):   # добавление элемента дистанции и элемента пользы в участки
                self.unos[i][j][3].append(0) 
                self.unos[i][j][4].append(0)
        self.dist_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)  # добавление карты дистанции
        self.sati_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)  # добавление карты пользы
        
        
    # ДОБАВЛЕНИЕ РЕСУРСА НА НЕСКОЛЬКО УЧАСТКОВ(номер ресурса, первая строка, первый столбец, последняя строка,
                                                                                                            #последний столбец)
    def add_resources(self, n, ff, fl, lf, ll, r = 1):
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Resource " + str(n)):
            for j in range(fl, ll+1):
                self.add_resource(n, i, j, r) # редактирование каждого участка по очереди
    
    # ДОБАВЛЕНИЕ РЕСУРСА НА УЧАСТОК (номер ресурса, строка участка, столбец участка)
    def add_resource(self, n, f, l, r = 1):
        self.unos[f][l][0][n] = r              # изменение индикатора этого ресурса у участков
        self.res_map[n][f][l] *= (1 + r)             # изменение карты ресурса
    
    
    # ОБЪЯВЛЕНИЕ УЧАСТКОВ РЕАЛЬНЫМИ (первая строка, первый столбец, последняя строка, последний столбец)
    def add_reals(self, ff, fl, lf, ll):  #ff fl - first coordinate, lf ll - last coordinate
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Real"):
            for j in range(fl, ll+1):
                self.add_real(i, j)        # редактирование каждого участка по очереди
    
    # ОБЪЯВЛЕНИЕ УЧАСТКА РЕАЛЬНЫМ (строка участка, столбец участка)
    def add_real(self, f, l): 
        self.unos[f][l][2] = 0                 # изменение номера принадлежности стране
        for k in range(len(self.res_map)):
            self.res_map[k][f][l] = 1          # изменение карт ресурсов
        if [f, l] not in self.transferable:
            self.transferable.append([f, l])   # добавление участка в множество свободных
    
    
    # ОБЪЯВЛЕНИЕ УЧАСТКОВ КОРНЯМИ СТРАНЫ(номер страны, первая строка, первый столбец, последняя строка, последний столбец)
    def add_roots(self, n, ff, fl, lf, ll): # ff, fl - 1st coor, lf, ll - 2nd coor
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Root of " + self.names[n]):
            for j in range(fl, ll+1):
                self.add_root(n, i, j)         # редактирование каждого участка по очереди
    
    # ОБЪЯВЛЕНИЕ УЧАСТКА КОРНЕМ СТРАНЫ(номер страны, строка участка, столбец участка)
    def add_root(self, n, f, l):
        if self.unos[f][l][2] == 0:                 # только если участок уже реален
            self.transferable.remove([f, l])        # убрать из множества передаваемых участков
            self.countries[n][2].append([f, l])  # добавить в множество корней страны
            self.unos[f][l][2] = n + 1              # изменить у участка номер принадлежности стране
            self.unos[f][l][1] = True               # изменить у участка индикатор корня или еез
            for k in range(len(self.countries)):    # изменить для всех карт недоступность участка
                if (k != n):
                    self.dist_map[k][f][l] = -2
                    self.sati_map[k][f][l] = -2
                else:
                    self.dist_map[k][f][l] = 0
                    self.sati_map[k][f][l] = 0
        
        
        
      ## ПРЕДОБРАБОТКА КАРТЫ ##
    
    
    # РАССЧИТЫВАЕТ РАССТОЯНИЯ И ПОЛЬЗЫ УЧАСТКОВ И РАСЧЁТ НАЧАЛЬНОГО УДОВЛЕТВОРЕНИЯ СТРАН
    def started_pack(self, d = 52.4):
        for k in range(len(self.countries)):
            self.started.append([])
            for i, j in self.countries[k][2]:
                z = self.z[i][j]
                if(((i == 0) or (self.unos[i-1][j][2] != k + 1)) or ((i == len(self.unos) - 1) or (self.unos[i+1][j][2] != k + 1)) or
                   ((j == 0) or (self.unos[i][j-1][2] != k + 1)) or ((j == len(self.unos[0]) - 1) or (self.unos[i][j+1][2] != k + 1))):
                    self.started[k].append([i, j, z])
        for i in tqdm_notebook(range(len(self.unos)), total=len(self.unos), desc="Started pack"):
            for j in range(len(self.unos[0])):
                if (self.unos[i][j][1] == False) and (self.unos[i][j][2] >= 0): # если участок может быть передан
                    for k in range(len(self.countries)):
                        dista = self.dist(i, j, k)              # рассчёт его полезности и расстония до страны k
                        self.unos[i][j][3][k] = dista        # изменение множества расстояний учатска
                        self.dist_map[k][i][j] = dista      # изменение карты расстояний
                    if min(self.unos[i][j][3]) > d:
                        for k in range(len(self.countries)):
                            satis = self.sati(i, j, k)
                            self.unos[i][j][4][k] = satis        # изменение множества пользы учатска
                            self.sati_map[k][i][j] = satis       # изменение карты польз
                            if self.percent:
                                self.full[k] += satis
                            else:
                                self.countries[k][1] -= satis        # изменение уровня удовлетворённости страны
                    else:
                        country = self.unos[i][j][3].index(min(self.unos[i][j][3]))
                        self.belong(i, j, country, 'EEZ ');        # передача участка стране
                        self.unos[i][j][1] = True;                 # изменение идентификатора корня или еез
                        self.transferable.remove([i, j])           # убирание из списка передаваемых
                        self.countries[country][4].append([i, j])  # добавление в список еез страны
                        self.unos[i][j][5] = True                  # изменение идентификатора еез
        if self.percent:
            for i in range(len(self.unos)):
                for j in range(len(self.unos[0])):
                    for k in range(len(self.countries)):
                        self.unos[i][j][4][k] = self.unos[i][j][4][k] / self.full[k] * 100
                        if self.sati_map[k][i][j] > 0:
                            self.sati_map[k][i][j] = self.sati_map[k][i][j] / self.full[k] * 100
        if self.percent == False:
            self.change_sati.append(np.array(self.countries)[:, 1].astype(int).tolist())# добавление первого множжества удовлетворённостей
        else:
            self.change_sati.append([round(x, 3) for x in np.array(self.countries)[:, 1]]) # добавление первого множжества удовлетворённостей
        self.start_map = np.array(self.unos)[:, :, 2].astype(int).tolist()         # добавление стартовой карты и стартовой карты с расширенной расцветкой
        self.start_map_diff = (np.array(self.unos)[:, :, 2].astype(int) * 3 - 2 * np.sign(np.array(self.unos)[:, :, 2].astype(int))).tolist()
        self.started = []

    
    
      ## ФУНКЦИИ ДЛЯ НАЧАЛЬНОГО РАЗДЕЛЕНИЯ КАРТЫ ##
    
    
    # ФУНКЦИЯ БЛИЗОСТИ отдаёт участки ближайшим странам
    def func_distance(self):
        for elem in tqdm_notebook(self.transferable, total= len(self.transferable), desc="Func Distance"):
            self.belong(elem[0], elem[1], self.near(elem[0], elem[1]), 'Func Distance ')  # передача участка ближайшей стране
        self.make_exch()                 # формируем карты для допустимого обмена

    
    # ФУНКЦИЯ ПОЛЬЗЫ отдаёт участки странам, которым они принесут больше пользы
    def func_satisfation(self):
        for elem in tqdm_notebook(self.transferable, total= len(self.transferable), desc="Func Satisfaction"):
            self.belong(elem[0], elem[1], self.most_sati(elem[0], elem[1]), 'Func Satisfaction ') # передача участка стране, которой он нужнее
        self.make_exch()                 # формируем карты для допустимого обмена
        
    
    # ФУНКЦИЯ СПРАВЕДЛИВОСТИ отдаёт самой бедной стране самый выгодный для неё участок и так по кругу
    def func_balance(self):
        empty = 0                              # индикатор того, что странам больше нечего передавать
        for k in tqdm_notebook(range(len(self.transferable) + len(self.countries) - 1), #пока не закончатся свободные участки
                               total= len(self.transferable) + len(self.countries) - 1, desc="Func Balance"):
            if empty == 0:                     # если есть ещё что передавать
                min_coun = self.min_sat()[1]   # находим страну с наименьшим уровнем удовлетворённости
                max_sati = 0                   # максимально возможная прибавка удовлетворённости
                maxf = 0                       # первая координата участка
                maxl = 0                       # вторая координата участка
                for elem in self.transferable: # для каждого свободного участка
                    i = elem[0]                # первая координата
                    j = elem[1]                # вторая координата
                    if (((i != 0 and (self.unos[i - 1][j][2] == min_coun + 1)) or   # есть ли у участка сосед из той страны
                        (j != 0 and (self.unos[i][j - 1][2] == min_coun + 1)) or
                        (j != len(self.unos[0]) - 1 and (self.unos[i][j + 1][2] == min_coun + 1)) or
                        (i != len(self.unos) - 1 and (self.unos[i + 1][j][2] == min_coun + 1))) 
                        and self.unos[i][j][2] == 0 and (max_sati < self.unos[i][j][4][min_coun] or  # лучше ли этот участок
                                                         (max_sati == self.unos[i][j][4][min_coun] and 
                                                  self.unos[maxf][maxl][3][min_coun] > self.unos[i][j][3][min_coun]))):
                        max_sati = self.unos[i][j][4][min_coun]     # теперь он лучший вариант
                        maxf = i                                    # записываем его первую координату
                        maxl = j                                    # записываем его вторую координату
                if max_sati != 0:                                   # если польза больше нуля, то отдаём
                    self.belong(maxf, maxl, min_coun, 'Func Balance ') 
                elif self.ind.count(0) > 1:                         # если польза нулевая, то переводим индикатор заполненности
                    self.ind[min_coun] = 1
                else:                                               # если все индикаторы включены, то обмен закончен
                    empty = 1                                       # переводим индикатор окончания обмена
                    for element in self.transferable:               # передаём оставшиеся участки ближайшим странам
                        if self.unos[element[0]][element[1]][2] == 0:
                            self.belong(element[0], element[1], self.near(element[0], element[1]), 'Func Balance ')
        for i in range(len(self.ind)):                              # возвращаем индикаторы self.ind в нулевое положение
            self.ind[i] = 0
        self.make_exch()                 # формируем карты для допустимого обмена
        
        
        
      ## ФУНКЦИИ ДОПОЛНИТЕЛЬНОЙ ОБРАБОТКИ
    
    
    # СПРАВЕДЛИВОСТЬ УВЕЛИЧИВАЕТ МИНИМАЛЬНУЮ УДОВЛЕТВОРЁННОСТЬ СТРАН ПОСРЕДСТВОМ CHARITY БОГАТЫЕ ОТДАЮТ БЕДНЫМ
    def charity(self):
        last_step = np.array(self.countries)[:, 1].astype(float)  # запоминание нынешнего состония уровня удовлетворённости
        self.total_charity()                                      # передаём участки от всех "богатых" ко всем "бедным"
        while ((np.array(self.countries)[:, 1].astype(float) != last_step).sum() != 0): # повтораяем пока меняются уровни удовлетворения
            last_step = np.array(self.countries)[:, 1].astype(float)
            self.total_charity()
        
    
    # ОБМЕН ПЫТАЕТСЯ ОБМЕНЯТЬСЯ МЕЖДУ ЛЮБЫМИ ДВУМЯ СТРАНАМИ НЕ УМЕНЬШАЯ УДОВЛЕТВОРЁННОСТЬ НИ ОДНОЙ ИЗ НИХ
        #количество случайных участков между которыми будет происходить обмен, количество попыток для каждой пары стран
    def exchange(self, sides = [8, 6, 4], attempts = 16, safe = False):
        succes = 1                                   # счётчик успешных обменов
        while succes != 0:                           # пока обмены происходят
            if safe:
                self.make_exch()                 # формируем карты для допустимого обмена 
            succes = 0                               # обнуляем счётчик обменов
            for i in range(len(self.countries)):
                for j in range(len(self.countries)): # для всех пар стран, между которыми возможен обмен
                    if i != j and len(self.list_exchange[i][j]) != 0 and len(self.list_exchange[j][i]) != 0 :
                        ntry = 0                     # обнуляем счётчик неудачных попыток
                        result = 0                   # обнуляем индикатор успеха обмена
                        while ntry != attempts:      # пока счётчик неудачных попыток не достиг количества попыток
                            result = self.exch(i, j, sides[0], sides[0], ntry)  #счётчик успеха = попытка обмена случайными участками 
                            if not result:           # если не удалось, повышаем счётчик неудачных попыток
                                ntry += 1
                            else:                    # иначе обнуляем счётчик неудачных попыток и включаем индикатор успешных обменов
                                ntry = 0
                                succes = 1
                        for elem in sides[1:]:
                            ntry = 0                     # обнуляем счётчик неудачных попыток
                            result = 0                   # обнуляем индикатор успеха обмена
                            while ntry != attempts:      # пока счётчик неудачных попыток не достиг количества попыток
                                result = self.exch(i, j,  elem, 2 * sides[0] - elem, ntry)  #счётчик успеха = попытка обмена случайными участками 
                                if not result:           # если не удалось, повышаем счётчик неудачных попыток
                                    ntry += 1
                                else:                    # иначе обнуляем счётчик неудачных попыток и включаем индикатор успешных обменов
                                    ntry = 0
                                    succes = 1
                            ntry = 0                     # обнуляем счётчик неудачных попыток
                            result = 0                   # обнуляем индикатор успеха обмена
                            while ntry != attempts:      # пока счётчик неудачных попыток не достиг количества попыток
                                result = self.exch(i, j,  2 * sides[0] - elem, elem, ntry)  #счётчик успеха = попытка обмена случайными участками 
                                if not result:           # если не удалось, повышаем счётчик неудачных попыток
                                    ntry += 1
                                else:                    # иначе обнуляем счётчик неудачных попыток и включаем индикатор успешных обменов
                                    ntry = 0
                                    succes = 1
                            
        
     
    # КОМБИНАЦИЯ СПРАВЕДЛИВОСТИ И ОБМЕНА
     #количество случайных участков для функции exchange между которыми будет происходить обмен, количество попыток обмена
    def char_exch(self, sides = [8, 6, 4], attempts = 16, safe = False):
        last_step = np.array(self.countries)[:, 1].astype(float) # запоминание нынешнего состония уровня удовлетворённости
        self.charity()                                           # передаём участки от "богатых" "бедным"
        self.exchange(sides, attempts, safe)                           # производим взаимовыгодный обмен
        while ((np.array(self.countries)[:, 1].astype(float) != last_step).sum() != 0): # пока меняются уровни удовлетворённости
            last_step = np.array(self.countries)[:, 1].astype(float)  # запоминание нынешнего уровня удовлетворённостей
            self.charity()                                      # передаём участки от "богатых" "бедным"
            self.exchange(sides, attempts, safe)                       # производим взаимовыгодный обмен
    
    
    
    
    def connectedness(self):
        self.transferable = []
        for i in range(len(self.countries)):
            root = self.countries[i][2] + self.countries[i][4]
            old = []
            new = []
            for k in tqdm_notebook(range(len(self.countries[i][2]) + len(self.countries[i][3]) + len(self.countries[i][4])), #пока не закончатся свободные участки
                               total= (len(self.countries[i][2]) + len(self.countries[i][3]) + len(self.countries[i][4])), desc="Connectedness" + self.names[i]):
                if root != []:
                    elem = [root[0][0] - 1, root[0][1]]
                    if (elem[0] >= 0) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                        new.append(elem)

                    elem = [root[0][0], root[0][1] - 1]
                    if (elem[1] >= 0) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                        new.append(elem)

                    elem = [root[0][0] + 1, root[0][1]]
                    if (elem[0] < len(self.unos)) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                        new.append(elem)

                    elem = [root[0][0], root[0][1] + 1]
                    if (elem[1] < len(self.unos[0])) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                        new.append(elem)

                    root = root[1:]

                else:
                    if new != []:
                        if new[0] not in old:
                            elem = [new[0][0] - 1, new[0][1]]
                            if (elem[0] >= 0) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                                new.append(elem)

                            elem = [new[0][0], new[0][1] - 1]
                            if (elem[1] >= 0) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                                new.append(elem)

                            elem = [new[0][0] + 1, new[0][1]]
                            if (elem[0] < len(self.unos)) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                                new.append(elem)

                            elem = [new[0][0], new[0][1] + 1]
                            if (elem[1] < len(self.unos[0])) and ((self.unos[elem[0]][elem[1]][2] - 1) == i) and (self.unos[elem[0]][elem[1]][1] == False) and (elem not in old) and (elem not in new):
                                new.append(elem)
                            old.append(new[0])
                        new = new[1:]
            copy_terr = copy.deepcopy(self.countries[i][3])
            for elem in copy_terr:
                if elem not in old:
                    self.transferable.append(elem)
                    self.countries[i][1] -= (2 - self.percent) * self.unos[elem[0]][elem[1]][4][i]
                    self.unos[elem[0]][elem[1]][2] = 0
                    self.countries[i][3].remove([elem[0], elem[1]])
                
    
    
      ## ФУНКЦИИ ДЛЯ ВЫВОДОВ
    
    # ПИШЕТ СТАТИСТИКУ РЕЗУЛЬТАТА ФУНКЦИИ exchange
    def exchange_info(self):
        di0 = sorted(new.exchanged[0].items(), key=lambda item: -item[1])
        di1 = sorted(new.exchanged[1].items(), key=lambda item: -item[1])
        di2 = sorted(new.exchanged[2].items(), key=lambda item: -item[1])
        print('Количество участков в настройках и количество таких обменов')
        for i in range(len(di0)):
            print(di0[i][0], di0[i][1])
        print('Количество участков от каждой страны, учавствующих в обмене и количество таких обменов')
        for i in range(len(di1)):
            print(di1[i][0], di1[i][1])
        print('Количество участков, учавствующих в обмене и количество таких обменов')
        for i in range(len(di2)):
            print(di2[i][0], di2[i][1])
    
    # ПИШЕТ ТАБЛИЦУ ЗАВИСТИ ГДЕ СТРАНА ИЗ СТРОКИ ЗАВИДУЕТ СТРАНЕ ИЗ СТОЛБЦА
    def envy_free(self):
        env = [['']]                           # таблица зависти
        for i in range(len(self.countries)):
            env[0].append(self.names[i])       # добавляем в таблицу верхнюю строку названий стран
        for i in range(len(self.countries)):
            env.append([self.names[i]])        # добавляем в таблицу левый столбец названий стран
            for j in range(len(self.countries)):
                env[i + 1].append(self.envy(i, j))  # заполняем таблицу
        max_len = max([len(str(e)) for r in env for e in r])
        for row in env:
            print(*list(map('{{:>{length}}}'.format(length= max_len).format, row)))  # выводим построчно таблицу
    
    
    # ПИШЕТ ТЕКУЩУЮ УДОВЛЕТВОРЁННОСТЬ СТРАН
    def countries_sati(self):
        sat_c = []                                               # список удовлетворённостей стран
        for i in range(len(self.countries)):                     
            sat_c.append([self.names[i], self.countries[i][1]])  # заполняем список удовлетворённостей
        max_len = max([len(str(e)) for r in sat_c for e in r])
        for row in sat_c:
            print(*list(map('{{:>{length}}}'.format(length= max_len).format, row))) #выводим список удовлетворённостей
    
    # СЛАЙДЕР ИЗМЕНЕНИЯ КАРТЫ  (рассматриваемый интервал, гистограмма, расширенная расцветка)
    def slider(self, interval = "All", hist = False, diff = True):
        if self.inline == 0:                         # настройка matplotlib
            %matplotlib inline
            self.inline = 1
            
        def update_iteration(value):                 # обновление итерации для слайдера
            update_map(iteration = value['new'])
        def update_map(iteration = 0):               # обновлеине карты
            clear_output(wait=True)                  # очистка вывода
            now_map = copy.deepcopy(start_map)       # начальная карта (в последствии к ней и будут применяться изменения)
            if diff:                                 # если расширенная расцветка
                for i in range(iteration):
                    now_map[change_map[i][0]][change_map[i][1]] = change_map[i][2] * 3 - (change_map[i][3] == "EEZ ") # изменяем карту
            else:                                    # если не расширенная
                for i in range(iteration):
                    now_map[change_map[i][0]][change_map[i][1]] = change_map[i][2] # изменяем карту
                    
            plt.imshow(now_map, cmap = cm.viridis)   # отображение карты
            plt.show()
                    
            if hist:                              # если гистограмма
                fig = plt.figure(figsize=(5, 5))     # настройка гистограммы
                mpl.rcParams.update({'font.size': 10})
                ax = plt.axes()
                ranges = (np.array(self.change_sati).max() - np.array(self.change_sati).min()) * 0.1
                plt.ylim([np.array(self.change_sati).min() - ranges, np.array(self.change_sati).max() + ranges])
                plt.xlim( -0.5, len(self.names))
                mpl.rcParams.update({'font.size': 10})
                for i in range(len(self.names)):
                    ax.text(i + 0.15, self.change_sati[start + iteration][i], self.change_sati[start + iteration][i])
                ax.yaxis.grid(True, zorder = 1)
                plt.bar([i for i in range(len(self.names))], self.change_sati[start+iteration], 
                        width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
                plt.xticks(range(len(self.names)), self.names, rotation=30)
                plt.legend(loc='upper right')
                
            slider = widgets.IntSlider(iteration, min = 0, max = len(change_map))  # слайдер итераций
            label = widgets.Label(value = 'Iterarion ' + str(iteration) + ((start!=0)*('(' + str(start + iteration) + ')')) + ' of ' + str(len(change_map)) + (' ' + change_map[slider.value - 1][3]) * (slider.value != 0))
            display(slider, label)
            slider.observe(update_iteration, names = 'value')

          #настройка рассматриваемого интервала  
        if interval == "All":                       # если интервал весь  
            start = 0
            end = len(self.change_map)
        elif isinstance(interval[0], int):          # если интервал задан численно
            if interval[0] < 0:
                interval[0] += len(self.change_map) 
            if interval[1] <= 0:
                interval[1] += len(self.change_map)
            start = interval[0]
            end = interval[1]
        else:                                       # если интервал задан названиями функций
            start = 0
            end = len(self.change_map)
            for i in range(len(self.change_map)):
                if self.change_map[i][3][:-1] in interval or self.change_map[i][3][:8] == 'Exchange' and 'Exchange' in interval:
                    start = i
                    break
            for i in range(len(self.change_map) - 1, -1, -1):
                if self.change_map[i][3][:-1] in interval or self.change_map[i][3][:8] == 'Exchange' and 'Exchange' in interval:
                    end = i + 1
                    break
        if diff:                                           # если расширенная расцветка
            start_map = copy.deepcopy(self.start_map_diff) # начальная карта
            for i in range(start):                         # применяем изменения
                start_map[self.change_map[i][0]][self.change_map[i][1]] = self.change_map[i][2] * 3 -  (self.change_map[i][3] == "EEZ ")
        else:                                              # если расцветка обычная
            start_map = copy.deepcopy(self.start_map)      # начальная карта
            for i in range(start):                         # применяем изменения
                start_map[self.change_map[i][0]][self.change_map[i][1]] = self.change_map[i][2]
        
        change_map = self.change_map[start:end]            # формируется список изменений

        plt.imshow(start_map, cmap = cm.viridis)           # отображение карты
        plt.show()
        if hist:                                        # если нужна гистограмма
            fig = plt.figure(figsize=(5, 5))               # формирование гистограммы
            mpl.rcParams.update({'font.size': 10})
            ax = plt.axes()
            ranges = (np.array(self.change_sati).max() - np.array(self.change_sati).min()) * 0.1
            plt.ylim([np.array(self.change_sati).min() - ranges, np.array(self.change_sati).max() + ranges])
            plt.xlim( -0.5, len(self.names))
            mpl.rcParams.update({'font.size': 10})
            for i in range(len(self.names)):
                ax.text(i + 0.15, self.change_sati[start][i], self.change_sati[start][i])
            ax.yaxis.grid(True, zorder = 1)
            plt.bar([i for i in range(len(self.names))], self.change_sati[start], 
                    width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
            plt.xticks(range(len(self.names)), self.names, rotation=30)
            plt.legend(loc='upper right')
        
        slider = widgets.IntSlider(0, min = 0, max = len(change_map))  # слайдер итераций
        label = widgets.Label(value = 'Iterarion 0' + ((start!=0)*('(' + str(start) + ')')) + ' of ' + str(len(change_map)) + (' ' + change_map[slider.value - 1][3]) * (slider.value != 0))
        display(slider, label)
        slider.observe(update_iteration, names = 'value')
        
    
    #3Д ОТОБРАЖЕНИЕ (интервал, расширенная настройка, пропуск участков, размер участков)
    def globus(self, interval = "All", diff = False, interv = 15, scale = 1.5):
        if self.inline >= 1:                   # настройка matplotlib
            for i in range(self.inline):
                
                %matplotlib notebook
            %matplotlib notebook
            self.inline = 0
            
        
          #настройка рассматриваемого интервала  
        if interval == "All":                       # если интервал весь  
            start = 0
            end = len(self.change_map)
        elif isinstance(interval[0], int):          # если интервал задан численно
            if interval[0] < 0:
                interval[0] += len(self.change_map) 
            if interval[1] <= 0:
                interval[1] += len(self.change_map)
            start = interval[0]
            end = interval[1]
        else:                                       # если интервал задан названиями функций
            start = 0
            end = len(self.change_map)
            for i in range(len(self.change_map)):
                if self.change_map[i][3][:-1] in interval or self.change_map[i][3][:8] == 'Exchange' and 'Exchange' in interval:
                    start = i
                    break
            for i in range(len(self.change_map) - 1, -1, -1):
                if self.change_map[i][3][:-1] in interval or self.change_map[i][3][:8] == 'Exchange' and 'Exchange' in interval:
                    end = i + 1
                    break
        if diff:                                           # если расширенная расцветка
            start_map = copy.deepcopy(self.start_map_diff) # начальная карта
            for i in range(start):                         # применяем изменения
                start_map[self.change_map[i][0]][self.change_map[i][1]] = self.change_map[i][2] * 3 -  (self.change_map[i][3] == "EEZ ")
        else:                                              # если расцветка обычная
            start_map = copy.deepcopy(self.start_map)      # начальная карта
            for i in range(start):                         # применяем изменения
                start_map[self.change_map[i][0]][self.change_map[i][1]] = self.change_map[i][2]
        
        change_map = self.change_map[start:end]            # формируется список изменений    
            
        x = []       # первая координата
        y = []       # вторая координата
        z = []       # третья координата
        colors = []  # массив цветов точек
        maxi = max(len(self.unos), len(self.unos[0]), max(max(self.z)) - min(min(self.z))) # максимальная длина координат
        if diff:                                                # рассчёт нужного смещения для размещения посередине
            for i in range(0, len(self.unos), interv):
                for j in range(0, len(self.unos[0]), interv):
                    if self.unos[i][j][2] > 0:
                        x.append((maxi - len(self.unos))/2 + i)
                        y.append((maxi - len(self.unos[0]))/2 + j)
                        z.append((maxi + max(max(self.z)))/2 - self.z[i][j])
                        colors.append(start_map[i][j])
        else:
            for i in range(0, len(self.unos), interv):
                for j in range(0, len(self.unos[0]), interv):
                    if self.unos[i][j][2] > 0:
                        x.append((maxi - len(self.unos))/2 + i)
                        y.append((maxi - len(self.unos[0]))/2 + j)
                        z.append((maxi + max(max(self.z)))/2 - self.z[i][j])
                        colors.append(start_map[i][j])

        fig = plt.figure(figsize=(5,5))                # настройка трёхмерной модели
        ax = fig.add_subplot(111, projection='3d')
        ax.set_xlabel('X axis')
        ax.set_ylabel('Y axis')
        ax.set_zlabel('Z axis')
        ax.set_xlim([0, maxi])
        ax.set_ylim([0, maxi])
        ax.set_zlim([0, maxi])
        ax.scatter(x, y, z,  c=colors, cmap=cm.viridis, s = 2 * interv * scale)
        ax.view_init(30, 30)
        plt.show()

        def update_plot(angle1 = 30, angle2 = 30):    # функция обновления угла
            self.angle1 = angle1
            self.angle2 = angle2
            ax.view_init(angle1, angle2)
            fig.canvas.draw_idle()

        angle1_slider = widgets.IntSlider(30, min = -180, max = 180)   # слайдер первого угла
        display(angle1_slider)
        
        angle2_slider = widgets.IntSlider(30, min = -180, max = 180)   # слайдер второго угла
        display(angle2_slider)
        
        slider = widgets.IntSlider(0, min = 0, max = len(change_map))  # слайдер итерации
        label = widgets.Label(value = 'Iterarion 0' + ((start!=0)*('(' + str(start) + ')')) + ' of ' + str(len(change_map)) + (' ' + change_map[slider.value - 1][3]) * (slider.value != 0))
        display(slider, label)

          # функции обновления для слайдеров
        def update_angle1(value):
            update_plot(angle1 = value['new'], angle2 = self.angle2)

        def update_angle2(value):
            update_plot(angle1 = self.angle1, angle2 = value['new'])
            
        def update_iteration(value):                 # обновление итерации
            update_map(iteration = value['new'])
        def update_map(iteration = 0):               # обновлеине карты
            clear_output(wait=True)                  # очистка вывода
            now_map = copy.deepcopy(start_map)       # начальная карта (в последствии к ней и будут применяться изменения)
            if diff:                                 # если расширенная расцветка
                for i in range(iteration):
                    now_map[change_map[i][0]][change_map[i][1]] = change_map[i][2] * 3 - (change_map[i][3] == "EEZ ") # изменяем карту
            else:                                    # если не расширенная
                for i in range(iteration):
                    now_map[change_map[i][0]][change_map[i][1]] = change_map[i][2] # изменяем карту
            
            colors = []
            for i in range(0, len(self.unos), interv):
                for j in range(0, len(self.unos[0]), interv):
                    if self.unos[i][j][2] > 0:
                        colors.append(now_map[i][j])
            fig = plt.figure(figsize=(5,5))
            ax = fig.add_subplot(111, projection='3d')
            ax.set_xlabel('X axis')
            ax.set_ylabel('Y axis')
            ax.set_zlabel('Z axis')
            ax.set_xlim([0, maxi])
            ax.set_ylim([0, maxi])
            ax.set_zlim([0, maxi])
            ax.scatter(x, y, z,  c=colors, cmap=cm.viridis, s = 2 * interv * scale)
            ax.view_init(self.angle1, self.angle2)
            plt.show()
            
            angle1_slider = widgets.IntSlider(self.angle1, min = -180, max = 180)
            display(angle1_slider)

            angle2_slider = widgets.IntSlider(self.angle2, min = -180, max = 180)
            display(angle2_slider)

            slider = widgets.IntSlider(iteration, min = 0, max = len(change_map))  # сам слайдер
            label = widgets.Label(value = 'Iterarion ' + str(iteration) + ((start!=0)*('(' + str(start + iteration) + ')')) + ' of ' + str(len(change_map)) + (' ' + change_map[slider.value - 1][3]) * (slider.value != 0))
            display(slider, label)
            
            def update_plot(angle1 = 30, angle2 = 30):
                self.angle1 = angle1
                self.angle2 = angle2
                ax.view_init(angle1, angle2)
                fig.canvas.draw_idle()

            def update_angle1(value):
                update_plot(angle1 = value['new'], angle2 = self.angle2)

            def update_angle2(value):
                update_plot(angle1 = self.angle1, angle2 = value['new'])
            
            angle1_slider.observe(update_angle1, names = 'value')
            angle2_slider.observe(update_angle2, names = 'value')
            slider.observe(update_iteration, names = 'value')
            

        angle1_slider.observe(update_angle1, names = 'value')
        angle2_slider.observe(update_angle2, names = 'value')
        slider.observe(update_iteration, names = 'value')

        
    
    
    # ТЕКУЩАЯ КАРТА (расширенная расцветка)
    def terr(self, diff = True):
        if self.inline == 0:     # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        if (diff):               # отображение карты
            plt.imshow(list(map(lambda a, b, c: list(map(lambda x, y, z: 2*x*(x>0) + x - 2 * y + z, a, b, c)), 
                                np.array(self.unos)[:, :, 2].astype(int), np.array(self.unos)[:, :, 1].astype(int), 
                               np.array(self.unos)[:, :, 5].astype(int))), cmap = cm.viridis)
        else:
            plt.imshow(np.array(self.unos)[:, :, 2].astype(int), cmap = cm.viridis)
        if self.percent == False:
            plt.title(str(len(self.change_map)) + ' ' + str(np.array(self.countries)[:, 1].astype(int)))
        else:
            plt.title(str(len(self.change_map)) + ' ' + str([round(x, 3) for x in np.array(self.countries)[:, 1]]))
        plt.show()
    
    # АНИМАЦИЯ ИЗМЕНЕНИЯ КАРТЫ необязательно указывать
       #(расширеная расцветкаб длительность каждого кадра в милисекундах, пропуск кадров, повторять анимацию?)
    def anim_terr(self, diff = True, interval = 200, x = 100, repeat = False):
        if self.inline >= 1:                           # настройка matplotlib
            for i in range(self.inline):
                %matplotlib notebook
            %matplotlib notebook
            self.inline = 0
        if diff:                                      # анимация
            f = plt.figure()
            ax = f.gca()
            im = copy.deepcopy(self.start_map_diff)
            image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis)
            def function_for_animation(frame_index):
                for i in range(x):
                    im[self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                     1)][0]][self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                                           1)][1]] = (self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][2] * 3 - (self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][3] == 'EEZ '))
                    image.set_data(im)
                ax.set_title(self.change_map[min(frame_index * x, len(self.change_map) - 1)][3] 
                             + str(min(frame_index * x, len(self.change_map) - 1)) + ' ' 
                             + str(self.change_sati[min(frame_index * x, len(self.change_map) - 1)]))
            
            return matplotlib.animation.FuncAnimation(f, function_for_animation, interval=interval, 
                                                      frames=(((len(self.change_map) - 1) // x) + 2), repeat = repeat, blit=True)
        else:
            f = plt.figure()
            ax = f.gca()
            im = copy.deepcopy(self.start_map)
            image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis)
            def function_for_animation(frame_index):
                for i in range(x):
                    im[self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                     1)][0]][self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                                           1)][1]] = self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][2]
                    image.set_data(im)
                ax.set_title(self.change_map[min(frame_index * x, len(self.change_map) - 1)][3] 
                             
                             + str(min(frame_index * x, len(self.change_map) - 1)) + ' ' 
                             + str(self.change_sati[min(frame_index * x, len(self.change_map) - 1)]))
            return matplotlib.animation.FuncAnimation(f, function_for_animation, interval=interval, 
                                                      frames=(((len(self.change_map) - 1) // x) + 2), repeat = repeat, blit = True)

    
    
    # ГИСТОГРАММА ТЕКУЩЕГО УДОВЛЕТВОРЕНИЯ СТРАН
    def hist(self):
        if self.inline == 0:           # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        fig = plt.figure(dpi = 80, figsize = (8, 4))     # гистограмма
        plt.title(str(len(self.change_sati)))
        mpl.rcParams.update({'font.size': 10})
        ax = plt.axes()
        plt.xlim( -0.5, len(self.names) - 0.5)
        for i in range(len(self.names)):
            if self.percent == False:
                ax.text(i + 0.15, np.array(self.countries)[:, 1].astype(int)[i], np.array(self.countries)[:, 1].astype(int)[i])
            else:
                ax.text(i + 0.15, round(np.array(self.countries)[i][1], 3), round(np.array(self.countries)[i][1], 3)) 
        ax.yaxis.grid(True, zorder = 1)
        if self.percent == False:
            plt.bar([x for x in range(len(self.names))], np.array(self.countries)[:, 1].astype(int), width = 0.3, color = 'blue',
                    alpha = 0.7, zorder = 2)
        else:
            plt.bar([x for x in range(len(self.names))], [round(x, 3) for x in np.array(self.countries)[:, 1]], width = 0.3, color = 'blue',
                   alpha = 0.7, zorder = 2)
        plt.xticks(range(len(self.names)), self.names)
        plt.legend(loc='upper right')
    
    
    # АНИМАЦИЯ ГИСТОГРАММЫ УДОВЛЕТВОРЕНИЯ необязательно
       #длительность каждого кадра в милисекундах, пропуск кадров, повторять анимацию?)
    def anim_hist(self, interval = 200, x = 1, repeat = False):
        if self.inline >= 1:                           # настройка matplotlib
            for i in range(self.inline):
                %matplotlib notebook
            %matplotlib notebook
            self.inline = 0
        fig = plt.figure(dpi = 80, figsize = (8, 4))  # анимация гистограммы
        ranges = (np.array(self.change_sati).max() - np.array(self.change_sati).min()) * 0.1
        def function_for_animation(frame_index):
            plt.clf()
            plt.title(self.change_map[min(frame_index * x, len(self.change_map) - 1)][3] + str(min(frame_index * x, len(self.change_map) - 1)))
            plt.ylim([np.array(self.change_sati).min() - ranges, np.array(self.change_sati).max() + ranges])
            plt.xlim( -0.5, len(self.names) - 0.5)
            mpl.rcParams.update({'font.size': 10})
            ax = plt.axes()
            for i in range(len(self.names)):
                ax.text(i + 0.15, self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i], 
                        self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i])
            ax.yaxis.grid(True, zorder = 1)
            plt.bar([x for x in range(len(self.names))], self.change_sati[min(frame_index * x, len(self.change_map) - 1)],
                    width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
            plt.xticks(range(len(self.names)), self.names)
            plt.legend(loc='upper right')
        return matplotlib.animation.FuncAnimation(fig, function_for_animation, interval=interval, repeat = repeat,
                                                  init_func = None,  frames=(((len(self.change_sati) - 1) // x) + 2), blit=True)
    
    
    # ТЕКУЩАЯ КАРТА И ГИСТОГРАММА УДОВЛеТВОРЕНИЯ СТРАН (расширенная расцветка)
    def terr_hist(self, diff = True):
        if self.inline == 0:                  # настройка matplotlib 
            %matplotlib inline
            self.inline = 1
        nrows = 1                            # фигура
        ncols = 2
        fig = plt.figure(figsize=(10, 5))
        ax = fig.add_subplot(nrows, ncols, 1)
        if diff:                              # карта
            plt.imshow(list(map(lambda a, b, c: list(map(lambda x, y, z: 2*x*(x>0) + x - 2 * y + z, a, b, c)), 
                    np.array(self.unos)[:, :, 2].astype(int), np.array(self.unos)[:, :, 1].astype(int), 
                    np.array(self.unos)[:, :, 5].astype(int))), cmap = cm.viridis)
        else:
            plt.imshow(np.array(self.unos)[:, :, 2].astype(int))
                                            # гистограмма
        if self.percent == False:
            plt.title(str(len(self.change_map)) + ' ' + str(np.array(self.countries)[:, 1].astype(int)))
        else:
            plt.title(str(len(self.change_map)) + ' ' + str([round(x, 3) for x in np.array(self.countries)[:, 1]]))
        plt.show()
        ax = fig.add_subplot(nrows, ncols, 2)
        plt.title(str(len(self.change_sati)))
        mpl.rcParams.update({'font.size': 10})
        plt.xlim( -0.5, len(self.names))
        for i in range(len(self.names)):
            if self.percent == False:
                ax.text(i + 0.15, np.array(self.countries)[:, 1].astype(int)[i], np.array(self.countries)[:, 1].astype(int)[i])
            else:
                ax.text(i + 0.15, round(np.array(self.countries)[i][1], 3), round(np.array(self.countries)[i][1], 3))
        ax.yaxis.grid(True, zorder = 1)
        if self.percent == False:
            plt.bar([x for x in range(len(self.names))], np.array(self.countries)[:, 1].astype(int), width = 0.3, color = 'blue',
                    alpha = 0.7, zorder = 2)
        else:
            plt.bar([x for x in range(len(self.names))], [round(x, 3) for x in np.array(self.countries)[:, 1]], width = 0.3, color = 'blue',
                   alpha = 0.7, zorder = 2)
        plt.xticks(range(len(self.names)), self.names)
        plt.legend(loc='upper right')
    
    
    # АНИМАЦИЯ КАРsТЫ И ГИСТОГРАММЫ необязательно 
            # расширенная расцветка, длительность каждого кадра в милисекундах, пропуск кадров, повторять анимацию?)
    def anim(self, diff = True, interval = 200, x = 1, repeat = False):
        if self.inline >= 1:                # настройка matplotlib
            for i in range(self.inline):
                %matplotlib notebook
            %matplotlib notebook
            self.inline = 0
        nrows = 1                          # фигура
        ncols = 2
        fig = plt.figure(figsize=(10, 5))
        ranges = (np.array(self.change_sati).max() - np.array(self.change_sati).min()) * 0.1
        if diff:                           # анимация карты и гистограммы
            im = copy.deepcopy(self.start_map_diff)
            def function_for_animation(frame_index):
                plt.clf()
                ax = fig.add_subplot(nrows, ncols, 2)
                plt.title(self.change_map[min(frame_index * x, len(self.change_map) - 1)][3] + str(min(frame_index * x, len(self.change_map) - 1)))
                plt.ylim([np.array(self.change_sati).min() - ranges, np.array(self.change_sati).max() + ranges])
                plt.xlim( -0.5, len(self.names))
                mpl.rcParams.update({'font.size': 10})
                for i in range(len(self.names)):
                    ax.text(i + 0.15, self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i], 
                            self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i])
                ax.yaxis.grid(True, zorder = 1)
                plt.bar([x for x in range(len(self.names))], self.change_sati[min(frame_index * x, len(self.change_map) - 1)], 
                        width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
                plt.xticks(range(len(self.names)), self.names, rotation=30)
                plt.legend(loc='upper right')
                ax = fig.add_subplot(nrows, ncols, 1)
                for i in range(x):
                    im[self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                     1)][0]][self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                                           1)][1]] = (self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][2] * 3 - (self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][3] == 'EEZ '))

                image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis)
                
                ax.set_title(self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][3] + str(min(frame_index * x, 
                                                                                                  len(self.change_map) - 1)) + ' ' + 
                             str(self.change_sati[min(frame_index * x, len(self.change_map) - 1)]))
        else:
            im = copy.deepcopy(self.start_map)
            def function_for_animation(frame_index):
                plt.clf()
                ax = fig.add_subplot(nrows, ncols, 2)
                plt.title(self.change_map[min(frame_index * x, len(self.change_map) - 1)][3] + str(min(frame_index * x, len(self.change_map) - 1)))
                plt.ylim([np.array(self.change_sati).min() - ranges, np.array(self.change_sati).max() + ranges])
                plt.xlim( -0.5, len(self.names))
                mpl.rcParams.update({'font.size': 10})
                for i in range(len(self.names)):
                    ax.text(i + 0.15, self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i], 
                            self.change_sati[min(frame_index * x, len(self.change_map) - 1)][i])
                ax.yaxis.grid(True, zorder = 1)
                plt.bar([x for x in range(len(self.names))], self.change_sati[min(frame_index * x, len(self.change_map) - 1)], 
                        width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
                plt.xticks(range(len(self.names)), self.names, rotation=30)
                plt.legend(loc='upper right')
                ax = fig.add_subplot(nrows, ncols, 1)
                for i in range(x):
                    im[self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                     1)][0]][self.change_map[min(frame_index * x + i, len(self.change_map) - 
                                                           1)][1]]= self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][2]
                image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis)
                ax.set_title(self.change_map[min(frame_index * x + i, len(self.change_map) - 1)][3] + str(min(frame_index * x, 
                                                                                                  len(self.change_map) - 1)) + ' ' + 
                             str(self.change_sati[min(frame_index * x, len(self.change_map) - 1)]))
        return matplotlib.animation.FuncAnimation(fig, function_for_animation, interval=interval, repeat = repeat,
                                                  init_func = None,  frames=(((len(self.change_sati) - 1) // x) + 2), blit=True)
    
    
    # КАРТА РЕСУРСА (номер ресурса)
    def map_resource(self, n):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        plt.imshow(np.array(self.res_map[n]), cmap = cm.viridis)
        plt.show()
    
    
    # КАРТА ВСЕХ РЕСУРСОВ ВМЕСТЕ
    def map_all_resources(self):
        if self.inline == 0:              # настройка matplotlib 
            %matplotlib inline
            self.inline = 1
        arr = self.res_map[0].copy()
        for i in range(len(self.res_map) - 1):
            arr += self.res_map[i + 1]
        plt.imshow(np.array(arr))
        plt.show()
    
    
    # ВСЕ КАРТЫ РЕСУРСОВ
    def map_resources(self):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        f, axarr = plt.subplots(len(self.res_map), 1)
        for i in range(len(self.res_map)):
            axarr[i].imshow(self.res_map[i])
        plt.show()
    
    
    # КАРТА РАССТОЯНИЯ ДЛЯ СТРАНЫ (номер страны)
    def map_dist(self, n):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        plt.imshow(np.array(self.dist_map[n]))
        plt.show()

    
    
    # КАРТА ПОЛЬЗЫ ДЛЯ СТРАНЫ (номер страны)
    def map_sati(self, n):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        plt.imshow(np.array(self.sati_map[n]))
        plt.show()

    
    
    # КАРТА ПОЛЬЗЫ И РАССТОЯНИЯ ДЛЯ СТРАНЫ (номер страны)
    def map_country(self, n):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        f, axarr = plt.subplots(1,2)
        axarr[0].imshow(self.dist_map[n])
        axarr[1].imshow(self.sati_map[n])
        plt.show()
    
    
    # ВСЕ КАРТЫ РАССТОЯНИЙ ДЛЯ СТРАН
    def map_dists(self):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        f, axarr = plt.subplots(len(self.countries), 1)
        for i in range(len(self.countries)):
            axarr[i].imshow(self.dist_map[i])
        plt.show()
    
    
    # ВСЕ КАРТЫ ПОЛЬЗЫ ДЛЯ СТРАН
    def map_satis(self):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        f, axarr = plt.subplots(len(self.countries), 1)
        for i in range(len(self.countries)):
            axarr[i].imshow(self.sati_map[i])
        plt.show()
    
    
    # ВСЕ КАРТЫ ПОЛЬЗ И РАССТОЯНИЙ ДЛЯ СТРАН
    def map_dists_satis(self):
        if self.inline == 0:              # настройка matplotlib
            %matplotlib inline
            self.inline = 1
        f, axarr = plt.subplots(len(self.countries), 2)
        for i in range(len(self.countries)):
            axarr[i, 0].imshow(self.dist_map[i])
            axarr[i, 1].imshow(self.sati_map[i])
        plt.show()
    
    
    
      ## СОХРАНЕНИЕ И ЗАГРУЗКА ДАННЫХ ##
        
    
    # СОХРАНИТЬ ТЕРРИТОРИЮ (указать название файла сохранения)
    def save(self, name):
        if(self.isave == 1):   # проверка индикатора для сохранения
            print('')          # вывод пустого сообщения 
            self.isave = 0
        sys.stdout.write("Saving...\r".format())
        sys.stdout.flush() 
        pd.DataFrame([pd.DataFrame(self.unos), pd.DataFrame(self.countries),    # сохранение всех переменных
                      pd.DataFrame([self.names]), pd.DataFrame([self.ind]), pd.DataFrame(self.d), 
                      pd.DataFrame(self.change_map), pd.DataFrame(self.change_sati), pd.DataFrame(self.start_map),
                      pd.DataFrame(self.start_map_diff), pd.DataFrame(self.transferable), pd.DataFrame(self.z),
                      pd.DataFrame([self.exchanged]), pd.DataFrame([self.full]),
                      pd.DataFrame([self.name, self.i_char, self.i_exch, self.isave, self.sphere,
                                    self.radius, self.inline, self.angle1, self.angle2, self.percent, self.i_exch2])
                      ]).to_pickle(name)
        
        print('Saved!   ')
    
    
    # ЗАГРУЗИТЬ ТЕРРИТОРИЮ (указать название файла)
    def load(self, name):
        if(self.isave == 1):      # проверка индикатора для сохранения
            print('')             # вывод пустого сообщения
            self.isave = 0
         # загрузка всех переменных
        sys.stdout.write("Loading.  \r".format())
        sys.stdout.flush()
        
        df = pd.read_pickle(name)
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.unos = df[0][0].values.tolist()
        sys.stdout.write("Loading...\r".format())
        sys.stdout.flush()
        
        self.countries =  df[0][1].values.tolist()
        sys.stdout.write("Loading.  \r".format())
        sys.stdout.flush()
        
        self.names = df[0][2].values[0].tolist()
        sys.stdout.write("Loading..  \r".format())
        sys.stdout.flush()
        
        self.ind = df[0][3].values[0].tolist()
        sys.stdout.write("Loading...  \r".format())
        sys.stdout.flush()
        
        self.d = df[0][4].values.tolist()
        sys.stdout.write("Loading.   \r".format())
        sys.stdout.flush()
        
        self.change_map = df[0][5].values.tolist()
        sys.stdout.write("Loading..  \r".format())
        sys.stdout.flush()
        
        self.change_jus = df[0][6].values.tolist()
        sys.stdout.write("Loading...  \r".format())
        sys.stdout.flush()
        
        self.start_map =df[0][7].values.tolist()
        sys.stdout.write("Loading.   \r".format())
        sys.stdout.flush()
        
        self.start_map_diff =df[0][8].values.tolist()
        sys.stdout.write("Loading..   \r".format())
        sys.stdout.flush()
        
        self.transferable =df[0][9].values.tolist()
        sys.stdout.write("Loading...   \r".format())
        sys.stdout.flush()  
        
        self.z =df[0][10].values.tolist()
        sys.stdout.write("Loading.   \r".format())
        sys.stdout.flush()
        
        self.name =df[0][11].values[0][0]
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.i_char =df[0][11].values[1][0]
        sys.stdout.write("Loading... \r".format())
        sys.stdout.flush()
        
        self.i_exch =df[0][11].values[2][0]
        sys.stdout.write("Loading.   \r".format())
        sys.stdout.flush()
        
        self.isave =df[0][11].values[3][0]
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.sphere =df[0][11].values[4][0]
        sys.stdout.write("Loading... \r".format())
        sys.stdout.flush()
        
        self.radius =df[0][11].values[5][0]
        sys.stdout.write("Loading.   \r".format())
        sys.stdout.flush()
        
        self.inline =df[0][11].values[6][0]
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.angle1 =df[0][11].values[7][0]
        sys.stdout.write("Loading... \r".format())
        sys.stdout.flush()
                
        self.angle2 =df[0][11].values[8][0]
        sys.stdout.write("Loading.  \r".format())
        sys.stdout.flush()
        
        self.percent =df[0][11].values[9][0]
        sys.stdout.write("Loading..  \r".format())
        sys.stdout.flush()
        
        self.i_exch2 =df[0][11].values[10][0]
        sys.stdout.write("Loading..  \r".format())
        sys.stdout.flush()
        
         #подсчёт карт ресурсов, расстояний и польз
        self.res_map = np.zeros((len(self.unos[0][0][0]), len(self.unos), len(self.unos[0])))
        self.dist_map = []
        self.saty_map = []
        for i in range(len(self.countries)):
            self.dist_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)
            self.saty_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):
                for k in range(len(self.unos[0][0][0])):
                    if self.unos[i][j][2] != -1:
                        self.res_map[k][i][j] += self.unos[i][j][0][k] + 1
                for k in range(len(self.countries)):
                    if self.unos[i][j][2] != -1:
                        if (self.unos[i][j][1] == False) or (self.unos[i][j][5] == True) or (self.unos[i][j][2] == k + 1):
                            self.dist_map[k][i][j] = self.unos[i][j][3][k]
                        else:
                            self.dist_map[k][i][j] = -2
                    else:
                        self.dist_map[k][i][j] = -1

                    if self.unos[i][j][2] != -1:
                        if (self.unos[i][j][1] == False) or (self.unos[i][j][5] == True) or (self.unos[i][j][2] == k + 1):
                            self.saty_map[k][i][j] = self.unos[i][j][4][k]
                        else:
                            self.saty_map[k][i][j] = -2
                    else:
                        self.saty_map[k][i][j] = -1
        sys.stdout.write("Loading...  \r".format())
        sys.stdout.flush()               
        self.make_exch()
    
        print('Loaded!   ')
    
    
    
        ### СИСТЕМНЫЕ ФУНКЦИИ ###(не для вызова и использования, но если аккуратно, то можно)
        
        
        
      ## СТАДНАРТНЫЕ РАССЧЁТЫ И ПРИСВОЕНИЯ ##
    
    
     # РАСЧЁТ РАССТОЯНИЯ ДЛЯ СТРАНЫ (строка участка, столбец участка, номер страны) возвращает минимально расстояние
    def dist(self, f, l, i_coun):
        if self.sphere:           # рассчёт для сферической модели
            d = np.linalg.norm(np.array(self.started[i_coun] - np.array([f, l, self.z[f][l]])), axis = 1).min()
            return math.acos(1 - 0.5*pow(d / self.radius, 2))*self.radius
        else:                     # рассчёт для плоской модели
            return np.linalg.norm(np.array(self.countries[i_coun][2][:, :2]) - np.array([f, l]), axis = 1).min()

    
    # РАСЧЁТ ПОЛЬЗЫ УЧАСТКА ДЛЯ СТРАНЫ (строка участка, столбец участка, номер страны)возвращает[пользая,
                                                                                                        #минимальное расстояние]
    def sati(self, f, l, i_cun):
        dista = self.unos[f][l][3][i_cun]  # рассчёт минимального расстояния
           # возвращает пользу участка стране и минимальное расстояние
        return max(0, ((np.array(self.unos[f][l][0]) * np.array(self.countries[i_cun][0])).sum() *
                    ((self.d[i_cun][1] - dista + 1)) 
                   / (self.d[i_cun][1] - min(dista, self.d[i_cun][0]) + 1)) ** 2)
    
    
    # БЛИЖАЙШАЯ К УЧАСТКУ СТРАНА (строка участка, столбец участка) возвращает номер ближайшей страны начиная с нуля
    def near(self, f, l):
        a = [[self.unos[f][l][3][i], -self.unos[f][l][4][i], self.countries[i][1]] for i in range(len(self.countries))]
        return a.index(min(a))
    
    
    # СТРАНА ДЛЯ КОТОРОЙ УЧАСТОК ПРИНЕСЁТ БОЛЬШЕ ПОЛЬЗЫ (строка участка, столбец участка) возвращает номер страны
    def most_sati(self, f, l):
        a = [[self.unos[f][l][4][i], -self.unos[f][l][3][i], -self.countries[i][1]] for i in range(len(self.countries))]
        return a.index(max(a))

    
    # ПРИСВОИТЬ УЧАСТОК СТРАНЕ (строка участка, столбец участка, номер сраны)
    def belong(self, f, l, i_cun, func = ''):
        if self.unos[f][l][2] > 0:                      # если страна уже принадлежит кому-то
            name_i = self.unos[f][l][2]                 # перемення прежней страны участка
            self.countries[name_i - 1][1] -= (2 - self.percent) * self.unos[f][l][4][name_i - 1]  # вычитаем двойную пользу участку у старой страны
            self.countries[name_i - 1][3].remove([f, l])# удаление участка из списка участков прежней страны
        self.unos[f][l][2] = i_cun + 1                  # смена информации о хозяине у участк
        if func != 'EEZ ':                              # если функция передачи не еез
            self.countries[i_cun][1] += (2 - self.percent) * self.unos[f][l][4][i_cun]  # добавление двойной пользы участка новой стране
            self.countries[i_cun][3].append([f, l])     # добавление участка в список участков страны
        if func[:8] != 'Exchange':
            self.change_map.append([f, l, i_cun + 1, func]) # добавление изменения в список изменения карты
        else:
            self.change_map.append([f, l, i_cun + 1, func + '(' + str(self.i_exch2) + ')']) # добавление изменения в список изменения карты
        if self.percent == False:
            self.change_sati.append(np.array(self.countries)[:, 1].astype(int).tolist()) # добавлеине изменения в список польз
        else:
            self.change_sati.append([round(x, 3) for x in np.array(self.countries)[:, 1]]) # добавлеине изменения в список польз
        if func == 'Charity ':                          # если функция передачи charity
            self.i_char += 1                            # изменяем счётчик i_char и пишем изменения
            sys.stdout.write("Charity: {0}, exchange: {1} ({4}), From {2} to {3}                  \r".format(str(self.i_char), 
                                                                                                      str(self.i_exch), 
                                                                                                      self.names[name_i - 1], 
                                                                                                      self.names[i_cun], self.i_exch2))
            sys.stdout.flush()
            self.isave = 1                              # меняем счётчик сохранения
        elif func[:8] == 'Exchange':                       # если функция передачи exchange
            self.i_exch += 1                            # изменяем счётчик i_exch и пишем изменения
            sys.stdout.write("charity: {0}, Exchange: {1} ({4}), {5} From {2} to {3}                  \r".format(str(self.i_char), 
                                                                                                      str(self.i_exch), 
                                                                                                      self.names[name_i - 1], 
                                                                                                      self.names[i_cun], 
                                                                                                      self.i_exch2, 
                                                                                                      func[9:]))
            sys.stdout.flush()
            self.isave = 1                              # меняем счётчик сохранения
            if (self.exchanged[0].get(int(func[8:])) == None):
                self.exchanged[0][int(func[8:])] = 1
            else:
                self.exchanged[0][int(func[8:])] += 1
        
    
      ## ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ДЛЯ CHARITY РАБОТАЮЩИЕ С SELF.IND ##
        
    
    # МИНИМАЛЬНО УДОВЛЕТВРЁННАЯ СТРАНА ИЗ ДОСТУПНЫХ = тех, у которых в self.ind соответсвуещему индексу сопоставлен 0 
    def min_sat(self):
        mini = self.countries[self.ind.index(0)][1]  # первая доступная страна
        answer = self.ind.index(0)                   # удовлетворённость первой доступной страны
        for i in range(1, len(self.countries)):
            if self.ind[i] == 0 and self.countries[i][1] < mini:  # если удовлетворённость ещё меньше
                mini = self.countries[i][1]                         # то она становится отвевтом
                answer = i
        return [mini, answer]                                       # возвращаем номер страны и её уровень удовлетворённости 
    
    
    # МАКСИМАЛЬНО УДОВЛЕТВОРЁННАЯ СТРАНА ИЗ ДОСТУПНЫХ
    def max_sat(self):
        maxi = self.countries[self.ind.index(0)][1]  # первая доступная страна
        answer = self.ind.index(0)                   # её удовлетворённость
        for i in range(1, len(self.countries)):
            if self.ind[i] == 0 and self.countries[i][1] > maxi: # если удовлетворённость ещё больше
                maxi = self.countries[i][1]                        # то она становится ответом
                answer = i
        return [maxi, answer]                                      # возвращаем номер страны и уровень удовлетворённости

    
    # МАКСИМАЛЬНО УДОВЛЕТВРЁННАЯ СТРАНА ИЗ НЕДОСТУПНЫХ
    def max_sat_re(self):
        maxi = self.countries[self.ind.index(1)][1]  # первая недоступная страна
        answer = self.ind.index(1)                   # уровень удовлетворённости первой недоступной страны
        for i in range(1, len(self.countries)):
            if self.ind[i] == 1 and self.countries[i][1] > maxi: # если удовлетворённость ещё больше
                maxi = self.countries[i][1]                          # то она становится ответом
                answer = i
        return [maxi, answer]                        # возвращаем номер страны и уровень удовлетворённости
    
    
    
      ## ВСПОМОГАТЕЛЬНЫЕ ДЛЯ ОБМЕНА И СПРАВЕДЛИВОСТИ
            
    # ФОРМИРУЕТ СПИСОК УЧАСТКОВ ДЛЯ ВЗАИМНОГО ОБМЕНА
    def make_exch(self):
        # формирование пустых списков
        self.list_exchange = [[[] for i in range(len(self.countries))] for i in range(len(self.countries))]
        self.map_exchange = [[[[] for i in range(len(self.unos[0]))] for i in range(len(self.unos))] for i in range(len(self.countries) + 1)]
        for i in range(len(self.unos)):         # проход по свободным участком и их запись в список готовых к обмену и в карту обмена
            for j in range(len(self.unos[0])):
                if ((not self.unos[i][j][1]) and self.unos[i][j][2] not in [-1, 0]):
                    if (i != 0 and (self.unos[i - 1][j][2] not in [-1, 0])):
                        if (self.unos[i][j][2] != self.unos[i - 1][j][2]):
                            self.list_exchange[self.unos[i][j][2] - 1][self.unos[i - 1][j][2] - 1].append([i, j])
                        self.map_exchange[self.unos[i - 1][j][2] - 1][i][j].append([-1, 0])
                    if (j != 0 and (self.unos[i][j - 1][2] not in [-1, 0])):
                        if (self.unos[i][j][2] != self.unos[i][j - 1][2] and len(self.map_exchange[self.unos[i][j - 1][2] - 1][i][j]) == 0):
                            self.list_exchange[self.unos[i][j][2] - 1][self.unos[i][j - 1][2] - 1].append([i, j])
                        self.map_exchange[self.unos[i][j - 1][2] - 1][i][j].append([0, -1])
                    if ((j != len(self.unos[0]) - 1) and (self.unos[i][j + 1][2] not in [-1, 0])):
                        if (self.unos[i][j][2] != self.unos[i][j + 1][2] and len(self.map_exchange[self.unos[i][j + 1][2] - 1][i][j]) == 0):
                            self.list_exchange[self.unos[i][j][2] - 1][self.unos[i][j + 1][2] - 1].append([i, j])
                        self.map_exchange[self.unos[i][j + 1][2] - 1][i][j].append([0, 1])
                    if ((i != len(self.unos) - 1) and (self.unos[i + 1][j][2] not in [-1, 0])):
                        if (self.unos[i][j][2] != self.unos[i + 1][j][2] and len(self.map_exchange[self.unos[i + 1][j][2] - 1][i][j] )== 0):
                            self.list_exchange[self.unos[i][j][2] - 1][self.unos[i + 1][j][2] - 1].append([i, j])
                        self.map_exchange[self.unos[i + 1][j][2] - 1][i][j].append([1, 0])
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):        # формирование карты обмена несвободных участков
                if ((self.unos[i][j][1]) or (self.unos[i][j][2] in [-1, 0])):
                    if (i != 0 and (self.unos[i - 1][j][2] not in [-1, 0]) and (not self.unos[i - 1][j][1])):
                        self.map_exchange[self.unos[i - 1][j][2] - 1][i][j].append([-1, 0])
                    if (j != 0 and (self.unos[i][j - 1][2] not in [-1, 0]) and (not self.unos[i][j - 1][1])):
                        self.map_exchange[self.unos[i][j - 1][2] - 1][i][j].append([0, -1])
                    if ((j != len(self.unos[0]) - 1) and (self.unos[i][j + 1][2] not in [-1, 0]) and (not self.unos[i][j + 1][1])):
                        self.map_exchange[self.unos[i][j + 1][2] - 1][i][j].append([0, 1])
                    if ((i != len(self.unos) - 1) and (self.unos[i + 1][j][2] not in [-1, 0]) and (not self.unos[i + 1][j][1])):
                        self.map_exchange[self.unos[i + 1][j][2] - 1][i][j].append([1, 0])
        
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):        # формирование списка опасных участков
                if ((not self.unos[i][j][1]) and self.unos[i][j][2] not in [-1, 0]):
                    if (len(self.map_exchange[self.unos[i][j][2] - 1][i][j]) == 1):
                        if (i != 0 and (self.unos[i - 1][j][2] == self.unos[i][j][2])):
                            self.map_exchange[-1][i - 1][j].append([1, 0])
                        elif ((i != len(self.unos) - 1) and (self.unos[i + 1][j][2] == self.unos[i][j][2])):
                            self.map_exchange[-1][i + 1][j].append([-1, 0])
                        elif ((j != len(self.unos) - 1) and (self.unos[i][j + 1][2] == self.unos[i][j][2])):
                            self.map_exchange[-1][i][j + 1].append([0, -1])
                        elif (j != 0 and (self.unos[i][j - 1][2] == self.unos[i][j][2])):
                            self.map_exchange[-1][i][j - 1].append([0, 1])                    

    # ВЗАИМОВЫГОДНЫЙ ОБМЕН СЛУЧАЙНЫМИ УЧАСТКАМИ МЕЖДУ ДВУМЯ СТАРАНАМИ
    def exch(self, one, two, sides1 = 8, sides2 = 8, ntry = 0):
        sys.stdout.write("charity: {0}, Exchange: {1} ({5}), {6} Try {4} from {2} to {3}                \r".format(str(self.i_char), 
                                                                                             str(self.i_exch), 
                                                                                             self.names[one], 
                                                                                             self.names[two], ntry,
                                                                                             self.i_exch2,
                                                                                             str(min(sides1, sides2))))
        first = []           # список готовых к обмену от первой страны
        second = []          # список готовых к обмену от второй страны
        firstsati = []       # список изменения удовлетворения стран от передачи участков первой страны
        secondsati = []      # список изменения удовлетворения стран от передачи участков второй страны
        constteamone = []    # условия для участков первой страны чтобы все соседи участка не ушли без него
        constteamtwo = []    # условия для участков второй страны чтобы все соседи участка не ушли без него
        constenemyone = []   # условия для участков первой страны чтобы все чужие соседи участка не стали своими, а этот не ушёл
        constenemytwo = []   # условия для участков второй страны чтобы все чужие соседи участка не стали своими, а этот не ушёл
         # номера случайных участков первой страны
        one_numbers = random.sample(range(len(self.list_exchange[one][two])), min(sides1, len(self.list_exchange[one][two])))
         # номера случайных участков второй страны
        two_numbers = random.sample(range(len(self.list_exchange[two][one])), min(sides2, len(self.list_exchange[two][one])))
          # заполнение множеств участков первой страны
        for elem in one_numbers:
            eleme = self.list_exchange[one][two][elem]
            if len(self.map_exchange[-1][eleme[0]][eleme[1]]) == 0:
                if eleme not in first:
                    first.append(eleme)
            else:
                no = 0
                for element in self.map_exchange[-1][eleme[0]][eleme[1]]:
                    if len(self.map_exchange[two][element[0] + eleme[0]][element[1] + eleme[1]]) == 0:
                        no = 1
                        break
                if no == 0:
                    if eleme not in first:
                        first.append(eleme)
                    for element in self.map_exchange[-1][eleme[0]][eleme[1]]:
                        if [element[0] + eleme[0], element[1] + eleme[1]] not in first:
                            first.append([element[0] + eleme[0], element[1] + eleme[1]])
            if len(first) >= sides1:
                break
         # заполнение множества участков второй страны
        for elem in two_numbers:
            eleme = self.list_exchange[two][one][elem]
            if len(self.map_exchange[-1][eleme[0]][eleme[1]]) == 0:
                if eleme not in second:
                    second.append(eleme)
            else:
                no = 0
                for element in self.map_exchange[-1][eleme[0]][eleme[1]]:
                    if len(self.map_exchange[one][element[0] + eleme[0]][element[1] + eleme[1]]) == 0:
                        no = 1
                        break
                if no == 0:
                    if eleme not in second:
                        second.append(eleme)
                    for element in self.map_exchange[-1][eleme[0]][eleme[1]]:
                        if [element[0] + eleme[0], element[1] + eleme[1]] not in second:
                            second.append([element[0] + eleme[0], element[1] + eleme[1]])
            if len(second) >= sides2:
                break
        

        
         # формирование списков условий первой страны
        for i in range(len(first)):
            team = len(self.map_exchange[one][first[i][0]][first[i][1]])
            teammates = []
            enemies = []
            enemy = len(self.map_exchange[two][first[i][0]][first[i][1]])
            for elem in self.map_exchange[one][first[i][0]][first[i][1]]:
                if ([elem[0] + first[i][0], elem[1] + first[i][1]] in first):
                    team -= 1
                    teammates.append(first.index([elem[0] + first[i][0], elem[1] + first[i][1]]))
                    if team == 0:
                        constteamone.append([i, teammates])
            for elem in self.map_exchange[two][first[i][0]][first[i][1]]:
                if ([elem[0] + first[i][0], elem[1] + first[i][1]] in second):
                    enemy -= 1
                    enemies.append(second.index([elem[0] + first[i][0], elem[1] + first[i][1]]))
                    if enemy == 0:
                        constenemyone.append([i, enemies])
         # формирование списков условий второй страны
        for i in range(len(second)):
            team = len(self.map_exchange[two][second[i][0]][second[i][1]])
            teammates = []
            enemies = []
            enemy = len(self.map_exchange[one][second[i][0]][second[i][1]])
            for elem in self.map_exchange[two][second[i][0]][second[i][1]]:
                if ([elem[0] + second[i][0], elem[1] + second[i][1]] in second):
                    team -= 1
                    teammates.append(second.index([elem[0] + second[i][0], elem[1] + second[i][1]]))
                    if team == 0:
                        constteamtwo.append([i, teammates])
            for elem in self.map_exchange[one][second[i][0]][second[i][1]]:
                if ([elem[0] + second[i][0], elem[1] + second[i][1]] in first):
                    enemy -= 1
                    enemies.append(first.index([elem[0] + second[i][0], elem[1] + second[i][1]]))
                    if enemy == 0:
                        constenemytwo.append([i, enemies])
         # заполнение множеств удовлетворений первой и второй страны
        for elem in first:
            firstsati.append([-self.unos[elem[0]][elem[1]][4][one], self.unos[elem[0]][elem[1]][4][two]])
        for elem in second:
            secondsati.append([self.unos[elem[0]][elem[1]][4][one], -self.unos[elem[0]][elem[1]][4][two]])
        if (len(first) == 0) or (len(second) == 0):  # если хоть кому-то нечем обмениваться, то заканчиваем
            return 0
        sati1 = firstsati + secondsati        # объединение множеств польз
        selection1 = cvxpy.Bool(len(sati1))   # идентификаторы обмена
        z = cvxpy.Variable()                  # переменная минимального изменения обмена
        a = len(first)
        constraint1 = [z <= np.array(sati1)[:, 1] * selection1, z <= np.array(sati1)[:, 0] * selection1] # условие поиска оптимума
         # добавление условий
        for elem in constteamone:
            constraint1.append(selection1[elem[0]] - cvxpy.sum_entries(selection1[elem[1]]) >= 1 - len(elem[1]))
        for elem in constteamtwo:
            constraint1.append(selection1[elem[0] + a] - cvxpy.sum_entries(selection1[[i + a for i in elem[1]]]) >=  1 - len(elem[1]))
        for elem in constenemyone:    
            constraint1.append(selection1[elem[0]] + cvxpy.sum_entries(selection1[[i + a for i in elem[1]]]) <= + len(elem[1]))
        for elem in constenemytwo:    
            constraint1.append(selection1[elem[0] + a] + cvxpy.sum_entries(selection1[elem[1]]) <=  len(elem[1]))
        total_utility1 = z   # оптимизируем z
        my_problem1 = cvxpy.Problem(cvxpy.Maximize(total_utility1), constraint1)
        my_problem1.solve(solver=cvxpy.GLPK_MI)  # решаем проблему
        first1 = (np.array(sati1)[:, 0] * selection1).value  # прибавление удовлетворённости первой страны
        second1 = (np.array(sati1)[:, 1] * selection1).value # прибавление удовлетворённости второй страны
        if (first1 != 0 or second1 != 0):             # если хоть одной из них лучше
            self.i_exch2 += 1                         # счётчик обменов увеличивает
            for j in range(len(selection1.value)):    # для всех переданных
                if selection1[j].value:
                    if j < a:                         # если от первой страны второй
                        
                        self.redact_exch(first[j][0], first[j][1], one, two) # учитываем влияение на карты допустимых обменов
                        
                        
                        self.belong(first[j][0], first[j][1], two, 'Exchange ' + str(min(sides1, sides2)))
                    else:                  # если от второй страны первой
                        j2 = j - a
                        
                        
                        self.redact_exch(second[j2][0], second[j2][1], two, one) # учитываем влияение на карты допустимых обменов
                        

                        
                        
                        
                        self.belong(second[j2][0], second[j2][1], one, 'Exchange ' + str(min(sides1, sides2)))
            exch_info = str(sorted([int(sum(selection1.value[:a])), int(sum(selection1.value[a:]))]))
            if self.exchanged[1].get(exch_info) == None:
                self.exchanged[1][exch_info] = 1
            else:
                self.exchanged[1][exch_info] += 1
                               
            if self.exchanged[2].get(int(sum(selection1.value))) == None:
                self.exchanged[2][int(sum(selection1.value))] = 1
            else:
                self.exchanged[2][int(sum(selection1.value))] += 1
                               
            return 1
        return 0
    
    # УЧЁТ ВЛИЯНИЕ ПЕРЕДАЧИ УЧАСТКА НА КАРТЫ ОПУСТИМЫХ ОБМЕНОВ (первая координата, вторая координата, от какой страны, какой стране)
    def redact_exch(self, first, last, one, two):
        if (first != 0) and (len(self.map_exchange[one][first - 1][last]) == 1) and (self.unos[first - 1][last][2] not in [one + 1, 0, -1]) and not self.unos[first - 1][last][1]:
            self.list_exchange[self.unos[first - 1][last][2] - 1][one].remove([first - 1, last])
        if (first != len(self.unos) - 1) and (len(self.map_exchange[one][first + 1][last]) == 1) and (self.unos[first + 1][last][2] not in [one + 1, 0, -1]) and not self.unos[first + 1][last][1]:
            self.list_exchange[self.unos[first + 1][last][2] - 1][one].remove([first + 1, last])
        if (last != 0) and (len(self.map_exchange[one][first][last - 1]) == 1) and (self.unos[first][last - 1][2] not in [one + 1, 0, -1]) and not self.unos[first][last - 1][1]:
            self.list_exchange[self.unos[first][last - 1][2] - 1][one].remove([first, last - 1])
        if (last != len(self.unos[0]) - 1) and (len(self.map_exchange[one][first][last + 1]) == 1) and (self.unos[first][last + 1][2] not in [one + 1, 0, -1]) and not self.unos[first][last + 1][1]:
            self.list_exchange[self.unos[first][last + 1][2] - 1][one].remove([first, last + 1])
        # добавить в список нового своих соседей
        if (first != 0) and (len(self.map_exchange[two][first - 1][last]) == 0) and (self.unos[first - 1][last][2] not in [two + 1, 0, -1]) and not self.unos[first - 1][last][1]:
            self.list_exchange[self.unos[first - 1][last][2] - 1][two].append([first - 1, last])
        if (first != len(self.unos) - 1) and (len(self.map_exchange[two][first + 1][last]) == 0) and (self.unos[first + 1][last][2] not in [two + 1, 0, -1]) and not self.unos[first + 1][last][1]:
            self.list_exchange[self.unos[first + 1][last][2] - 1][two].append([first + 1, last])
        if (last != 0) and (len(self.map_exchange[two][first][last - 1]) == 0) and (self.unos[first][last - 1][2] not in [two + 1, 0, -1]) and not self.unos[first][last - 1][1]:
            self.list_exchange[self.unos[first][last - 1][2] - 1][two].append([first, last - 1])
        if (last != len(self.unos[0]) - 1) and (len(self.map_exchange[two][first][last + 1]) == 0) and (self.unos[first][last + 1][2] not in [two + 1, 0, -1]) and not self.unos[first][last + 1][1]:
            self.list_exchange[self.unos[first][last + 1][2] - 1][two].append([first, last + 1])
        # убрать себя из списка соседей и добавить нового себя в список соседей
        team1 = []
        enemy1 = []
        if (first != 0) and (self.unos[first - 1][last][2] not in [-1, 0]):
            if self.unos[first - 1][last][2] != one + 1:
                team1.append(self.unos[first - 1][last][2])
            if self.unos[first - 1][last][2] != two + 1:
                enemy1.append(self.unos[first - 1][last][2])
        if (first != len(self.unos) - 1) and (self.unos[first + 1][last][2] not in [-1, 0]):
            if self.unos[first + 1][last][2] != one + 1:
                team1.append(self.unos[first + 1][last][2])
            if self.unos[first + 1][last][2] != two + 1:
                enemy1.append(self.unos[first + 1][last][2])
        if (last != 0) and (self.unos[first][last - 1][2] not in [-1, 0]):
            if self.unos[first][last - 1][2] != one + 1:
                team1.append(self.unos[first][last - 1][2])
            if self.unos[first][last - 1][2] != two + 1:
                enemy1.append(self.unos[first][last - 1][2])
        if (last != len(self.unos[0]) - 1) and (self.unos[first][last + 1][2] not in [-1, 0]):
            if self.unos[first][last + 1][2] != one + 1:
                team1.append(self.unos[first][last + 1][2])
            if self.unos[first][last + 1][2] != two + 1:
                enemy1.append(self.unos[first][last + 1][2])
        for elem in list(set(team1)):
            self.list_exchange[one][elem - 1].remove([first, last])
        for elem in list(set(enemy1)):
            self.list_exchange[two][elem - 1].append([first, last])



        self.map_exchange[-1][first][last] = [] #обнуление своего счётчика

        # составление своего счётчика
        if (first != 0) and (self.map_exchange[two][first - 1][last] == []) and (self.unos[first - 1][last][2] == two + 1) and not self.unos[first - 1][last][1]:
            self.map_exchange[-1][first][last].append([-1, 0])
        if (first != len(self.unos) - 1) and (self.map_exchange[two][first + 1][last] == []) and (self.unos[first + 1][last][2] == two + 1) and not self.unos[first + 1][last][1]:
            self.map_exchange[-1][first][last].append([1, 0])
        if (last != 0) and (self.map_exchange[two][first][last - 1] == []) and (self.unos[first][last - 1][2] == two + 1) and not self.unos[first][last - 1][1]:
            self.map_exchange[-1][first][last].append([0, -1])
        if (last != len(self.unos[0]) - 1) and (self.map_exchange[two][first][last + 1] == []) and (self.unos[first][last + 1][2] == two + 1) and not self.unos[first][last + 1][1]:
            self.map_exchange[-1][first][last].append([0, 1])

        if len(self.map_exchange[one][first][last]) == 1:    #обнуление счётчика бывшего
            self.map_exchange[-1][self.map_exchange[one][first][last][0][0] + first][self.map_exchange[one][first][last][0][1] + last].remove([-self.map_exchange[one][first][last][0][0], -self.map_exchange[one][first][last][0][1]])

        # возможно сам стал опасным
        if len(self.map_exchange[two][first][last]) == 1:
            self.map_exchange[-1][self.map_exchange[two][first][last][0][0] + first][self.map_exchange[two][first][last][0][1] + last].append([-self.map_exchange[two][first][last][0][0], -self.map_exchange[two][first][last][0][1]])



        # возможно спас новых опасных
        if (first != 0) and (len(self.map_exchange[two][first - 1][last]) == 1) and (self.unos[first - 1][last][2] == two + 1) and not self.unos[first - 1][last][1]:
            self.map_exchange[-1][self.map_exchange[two][first - 1][last][0][0] + first - 1][self.map_exchange[two][first - 1][last][0][1] + last].remove([-self.map_exchange[two][first - 1][last][0][0], -self.map_exchange[two][first - 1][last][0][1]])
        if (first != len(self.unos) - 1) and (len(self.map_exchange[two][first + 1][last]) == 1) and (self.unos[first + 1][last][2] == two + 1) and not self.unos[first + 1][last][1]:
            self.map_exchange[-1][self.map_exchange[two][first + 1][last][0][0] + first + 1][self.map_exchange[two][first + 1][last][0][1] + last].remove([-self.map_exchange[two][first + 1][last][0][0], -self.map_exchange[two][first + 1][last][0][1]])
        if (last != 0) and (len(self.map_exchange[two][first][last - 1]) == 1) and (self.unos[first][last - 1][2] == two + 1) and not self.unos[first][last - 1][1]:
            self.map_exchange[-1][self.map_exchange[two][first][last - 1][0][0] + first][self.map_exchange[two][first][last - 1][0][1] + last - 1].remove([-self.map_exchange[two][first][last - 1][0][0], -self.map_exchange[two][first][last - 1][0][1]])
        if (last != len(self.unos[0]) - 1) and (len(self.map_exchange[two][first][last + 1]) == 1) and (self.unos[first][last + 1][2] == two + 1) and not self.unos[first][last + 1][1]:
            self.map_exchange[-1][self.map_exchange[two][first][last + 1][0][0] + first][self.map_exchange[two][first][last + 1][0][1] + last + 1].remove([-self.map_exchange[two][first][last + 1][0][0], -self.map_exchange[two][first][last + 1][0][1]])

        # удаление старых соседств и прибавление новых
        if first != 0:
            self.map_exchange[one][first - 1][last].remove([1, 0])
            self.map_exchange[two][first - 1][last].append([1, 0])
        if first != len(self.unos) - 1:
            self.map_exchange[one][first + 1][last].remove([-1, 0])
            self.map_exchange[two][first + 1][last].append([-1, 0])
        if last != 0:
            self.map_exchange[one][first][last - 1].remove([0, 1])
            self.map_exchange[two][first][last - 1].append([0, 1])
        if last != len(self.unos[0]) - 1:
            self.map_exchange[one][first][last + 1].remove([0, -1])
            self.map_exchange[two][first][last + 1].append([0, -1])


        # возможно сделал опасными старых
        if (first != 0) and (len(self.map_exchange[one][first - 1][last]) == 1) and (self.unos[first - 1][last][2] == one + 1) and not self.unos[first - 1][last][1]:
            self.map_exchange[-1][self.map_exchange[one][first - 1][last][0][0] + first - 1][self.map_exchange[one][first - 1][last][0][1] + last].append([-self.map_exchange[one][first - 1][last][0][0], -self.map_exchange[one][first - 1][last][0][1]])
        if (first != len(self.unos) - 1) and (len(self.map_exchange[one][first + 1][last]) == 1) and (self.unos[first + 1][last][2] == one + 1) and not self.unos[first + 1][last][1]:
            self.map_exchange[-1][self.map_exchange[one][first + 1][last][0][0] + first + 1][self.map_exchange[one][first + 1][last][0][1] + last].append([-self.map_exchange[one][first + 1][last][0][0], -self.map_exchange[one][first + 1][last][0][1]])
        if (last != 0) and (len(self.map_exchange[one][first][last - 1]) == 1) and (self.unos[first][last - 1][2] == one + 1) and not self.unos[first][last - 1][1]:
            self.map_exchange[-1][self.map_exchange[one][first][last - 1][0][0] + first][self.map_exchange[one][first][last - 1][0][1] + last - 1].append([-self.map_exchange[one][first][last - 1][0][0], -self.map_exchange[one][first][last - 1][0][1]])
        if (last != len(self.unos[0]) - 1) and (len(self.map_exchange[one][first][last + 1]) == 1) and (self.unos[first][last + 1][2] == one + 1) and not self.unos[first][last + 1][1]:
            self.map_exchange[-1][self.map_exchange[one][first][last + 1][0][0] + first][self.map_exchange[one][first][last + 1][0][1] + last + 1].append([-self.map_exchange[one][first][last + 1][0][0], -self.map_exchange[one][first][last + 1][0][1]]) 

    
    # ОТДАЁТ САМЫЙ ВЫГОДНЫЙ УЧАСТОК ВТОРОЙ СТРАНЫ ПЕРВОЙ СТРАНЕ (номер первой и второй страны) возвращает индексы участка 
    def chari(self, maxi_i, mini_i):                                                        # и номер второй страны
        sys.stdout.write("Charity: {0}, exchange: {1} ({4}), Try from {2} to {3}                  \r".format(str(self.i_char), 
                                                                                                      str(self.i_exch), 
                                                                                                      self.names[maxi_i], 
                                                                                                      self.names[mini_i], self.i_exch2))
        ind_max = 0   # индекс найденного максимума
        maximum = 0   # максимальная относительная разница пользы
        for i in self.list_exchange[maxi_i][mini_i]:  # проходим по всем участкам второй страны
            firs = i[0]
            las = i[1]
            if ([self.countries[mini_i][1], self.countries[maxi_i][1]] < [self.countries[maxi_i][1] - 2 * self.unos[firs][las][4][maxi_i], self.countries[mini_i][1] + 2 * self.unos[firs][las][4][mini_i]]
                and # если имеет смысл передать
                # если её относительная польза больше
                maximum < (self.unos[firs][las][4][mini_i] / (self.unos[firs][las][4][maxi_i] + sys.float_info.epsilon))):
                maximum = (self.unos[firs][las][4][mini_i] / (self.unos[firs][las][4][maxi_i] + sys.float_info.epsilon))
                ind_max = i    # в индекс записывается очерёдность выбранного участка в множестве
        if (ind_max != 0):         # если максимум найден
            self.redact_exch(ind_max[0], ind_max[1], maxi_i, mini_i) # учитываем влияение на карты допустимых обменов
            self.belong(ind_max[0], ind_max[1], mini_i, 'Charity ')  # передаём участок
            return 1 #возвращаем что передали и номер второго участка
        return 0
    
    
    # ОТ САМОЙ БОГАТОЙ СТРАНЕ ОТДАЁТ БЕДНОЙ С ПОМОЩЬЮ CHARITY
    def one_charity(self):
        min1 = self.min_sat()[1]                   # запоминаем страну с наименьшей удовлеторённостью
        max1 = self.max_sat()[1]                   # запоминаем страну с наибольшей удовлетворённостью
        result = self.chari(max1, min1)                 # запоминаем что передали
        while result:       # пока имеет смысл отдавать
            min1 = self.min_sat()[1]               #повторяем
            max1 = self.max_sat()[1] 
            result = self.chari(max1, min1)
    
    
    # ОТ ВСЕХ СТРАН ОТДАЁТ САМОЙ БЕДНОЙ
    def all_charity(self):
        maxsat = self.max_sat()[1]          # запоминаем самую богатую страну
        self.one_charity()                  # от самой богатой отдаём самой бедной
        self.ind[maxsat] = 1                # блокируем самую богатую
        if self.ind.count(0) > 1:           # если ещё есть кому отдавать, то повторяем
            self.all_charity()
        self.ind[self.max_sat_re()[1]] = 0  # возвращаем индикатор обратно
    
    
    # ОТ ВСЕХ СТРАН ОТДАЁТ ВСЕМ(БОГАТЕЙШИЕ БЕДНЕЙШИМ)
    def total_charity(self):
        minsat = self.min_sat()[1]          # запоминаем самую бедную страну
        self.all_charity()                  # производим обмен от всех ей
        self.ind[minsat] = 1                # блокируем её
        if self.ind.count(0) > 1:           # повтораяем с другой пока есть страны
            self.total_charity()
        else:
            for i in range(len(self.ind)):  # обнуляем инндикаторы
                self.ind[i] = 0
    
    
      ## ВСПОМОГАТЕЛНЫЕ ФУНКЦИИ ДЛЯ ВЫВОДОВ
        
    
    # ЗАВИСТЬ ПЕРВОЙ СТРАНЫ ВТОРОЙ СТРАНЕ (номер первой страны, номер второй страны)
    def envy(self, coun_1, coun_2): 
        result = 0   # результат
        for i in range(len(self.countries[coun_1][3])): # учитываем участки первой страны
            result += self.unos[self.countries[coun_1][3][i][0]][self.countries[coun_1][3][i][1]][4][coun_1]
        for i in range(len(self.countries[coun_2][3])): # учитываем участки второй страны
            result -= self.unos[self.countries[coun_2][3][i][0]][self.countries[coun_2][3][i][1]][4][coun_1]
        if self.percent == False:
            return int(result)
        return round(result, 3)
