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






%matplotlib notebook
class Territory:
    def __init__(self, name, row, coloumn, resources):  # объявление территории(Название, высота, ширина, кол-во ресурсов)
        
        
        self.unos = [None] * row    # mассив элементов территории
        for i in range(row):
            self.unos[i] = [None] * coloumn
            for j in range(coloumn):
                self.unos[i][j] = [[False] * resources, False, -1, [], []] # [ресурсы,], корень?, страна+1, [дистанции],
                                                                                                                     #[польза]
        self.countries = []   # массив стран
        self.name = name      # название территории
        self.names = []       # название стран
        self.jus = []         # массив отображения стран нужный для justice и fun_justice
        self.d = []           # границы полезности
        self.anim = []        # массив изменения карты для анимации
        self.anim2 = []       # массив удовлетворения стран для гистограммы
        self.anima = []       # первый вариант карты
        self.res_map = np.zeros((resources, row, coloumn))  # карты ресурсов
        self.dist_map = []    # карта расстояние
        self.saty_map = []    # карта полезностей
        self.real_not_root = []   # массив реальных элементов не являющихся корнями(свободных)
        self.ij = 0           # счётчик для justice
        self.ie = 0           # счётчик для exchange
        self.ije = 0          # счётчик для сохранения карты
        
        
        ### ПОЛЬЗОВАТЕЛЬСКИЕ ФУНКЦИИ ###
        
        
        
      ## РЕДАКТИРОВАНИЕ КАРТЫ ## 
        
        
    # ДОБАВЛЕНИЕ СТРАНЫ (название, приоритеты, границы пользы)
    def add_country(self, name, priorities, dis):
        self.countries.append([priorities, 0, [], []]) # приоритеты удовлетворение корни территоии 
        self.jus.append(0)
        self.names.append(name)
        self.d.append(dis)
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):
                self.unos[i][j][3].append(0)
                self.unos[i][j][4].append(0)
        self.dist_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)
        self.saty_map.append(np.ones((len(self.unos), len(self.unos[0]))) * -1)
        
        
    # ДОБАВЛЕНИЕ РЕСУРСА НА НЕСКОЛЬКО УЧАСТКОВ(номер ресурса, первая строка, первый столбец, последняя строка,
                                                                                                            #последний столбец)
    def add_resources(self, n, ff, fl, lf, ll):
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Resource " + str(n)):
            for j in range(fl, ll+1):
                self.unos[i][j][0][n] = True
                self.res_map[n][i][j] *= 2
    
    # ДОБАВЛЕНИЕ РЕСУРСА НА УЧАСТОК (номер ресурса, строка участка, столбец участка)
    def add_one_resource(self, n, f, l):
        self.unos[f][l][0][n] = True
        self.res_map[n][f][l] *= 2
    
    
    # ОБЪЯВЛЕНИЕ УЧАСТКОВ РЕАЛЬНЫМИ (первая строка, первый столбец, последняя строка, последний столбец)
    def add_real(self, ff, fl, lf, ll):  #ff fl - first coordinate, lf ll - last coordinate
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Real"):
            for j in range(fl, ll+1):
                self.add_one_real(i, j)
    
    # ОБЪЯВЛЕНИЕ УЧАСТКА РЕАЛЬНЫМ (строка участка, столбец участка)
    def add_one_real(self, f, l):
        self.unos[f][l][2] = 0
        for k in range(len(self.res_map)):
            self.res_map[k][f][l] = 1
        if [f, l] not in self.real_not_root:
            self.real_not_root.append([f, l])
    
    
    # ОБЪЯВЛЕНИЕ УЧАСТКОВ КОРНЯМИ СТРАНЫ(номер страны, первая строка, первый столбец, последняя строка, последний столбец)
    def root_country(self, n, ff, fl, lf, ll): # ff, fl - 1st coor, lf, ll - 2nd coor
        for i in tqdm_notebook(range(ff, lf+1), total= lf + 1 - ff, desc="Add Root of " + self.names[n]):
            for j in range(fl, ll+1):
                self.root_one(n, i, j)
    
    # ОБЪЯВЛЕНИЕ УЧАСТКА КОРНЕМ СТРАНЫ(номер страны, строка участка, столбец участка)
    def root_one(self, n, f, l):
        if self.unos[f][l][2] == 0:
            self.real_not_root.remove([f, l])
            self.countries[n][2].append([f, l])
            self.unos[f][l][2] = n + 1
            self.unos[f][l][1] = True
            for k in range(len(self.countries)):
                if (k != n):
                    self.dist_map[k][f][l] = -2
                    self.saty_map[k][f][l] = -2
                else:
                    self.dist_map[k][f][l] = 0
                    self.saty_map[k][f][l] = 0
        
        
        
      ## ПРЕДОБРАБОТКА КАРТЫ ##
    
    
    # РАССЧИТЫВАЕТ РАССТОЯНИЯ И ПОЛЬЗЫ УЧАСТКОВ
    def started_pack(self):
        for i in tqdm_notebook(range(len(self.unos)), total=len(self.unos), desc="Started pack"):
            for j in range(len(self.unos[0])):
                if (self.unos[i][j][1] == False) and (self.unos[i][j][2] >= 0):
                    for k in range(len(self.countries)):
                        satys = self.saty(i, j, k)
                        self.unos[i][j][3][k] = satys[1]
                        self.unos[i][j][4][k] = satys[0]
                        self.dist_map[k][i][j] = satys[1]
                        self.saty_map[k][i][j] = satys[0]
        # РАССЧЁТ НАЧАЛЬНОГО УДОВЛЕТВОРЕНИЯ СТРАН
        for i in tqdm_notebook(range(len(self.unos)), total=len(self.unos), desc="Started pack 2"):
            for j in range(len(self.unos[0])):
                if (self.unos[i][j][1] == False) and (self.unos[i][j][2] >= 0):
                    for k in range(len(self.countries)):
                        self.countries[k][1] -= self.unos[i][j][4][k]
        self.anima = np.array(self.unos)[:, :, 2].astype(int).tolist()
    
    
    
      ## ФУНКЦИИ ДЛЯ НАЧАЛЬНОГО РАЗДЕЛЕНИЯ КАРТЫ ##
    
    
    # ФУНКЦИЯ БЛИЗОСТИ отдаёт участки ближайшим странам
    def fun_near(self):
        for elem in tqdm_notebook(self.real_not_root, total= len(self.real_not_root), desc="Fun Near"):
            self.belong(elem[0], elem[1], self.near(elem[0], elem[1]), 'Fun Near ')

    
    # ФУНКЦИЯ ПОЛЬЗЫ отдаёт участки странам, которым они принесут больше пользы
    def fun_saty(self):
        for elem in tqdm_notebook(self.real_not_root, total= len(self.real_not_root), desc="Fun Saty"):
            self.belong(elem[0], elem[1], self.most_saty(elem[0], elem[1]), 'Fun Saty ')
        
    
    # ФУНКЦИЯ СПРАВЕДЛИВОСТИ отдаёт самой бедной стране самый выгодный для неё участок и так по кругу
    def fun_justice(self):
        boo = 0
        for k in tqdm_notebook(range(len(self.real_not_root) + len(self.countries) - 1), 
                               total= len(self.real_not_root) + len(self.countries) - 1, desc="Fun Justice"):
            if boo == 0:
                mini = self.min_sat()[1]
                maxi = 0
                maxf = 0
                maxl = 0
                for elem in self.real_not_root:
                    i = elem[0]
                    j = elem[1]
                    if (((i != 0 and (self.unos[i - 1][j][2] == mini + 1)) or
                        (j != 0 and (self.unos[i][j - 1][2] == mini + 1)) or
                        (j != len(self.unos[0]) - 1 and (self.unos[i][j + 1][2] == mini + 1)) or
                        (i != len(self.unos) - 1 and (self.unos[i + 1][j][2] == mini + 1))) 
                        and self.unos[i][j][2] == 0 and (maxi < self.unos[i][j][4][mini] or 
                                                         (maxi == self.unos[i][j][4][mini] and 
                                                  self.unos[maxf][maxl][3][mini] > self.unos[i][j][3][mini]))):
                        maxi = self.unos[i][j][4][mini]
                        maxf = i
                        maxl = j
                if maxi != 0:
                    self.belong(maxf, maxl, mini, 'Fun Justice ')
                elif self.jus.count(0) > 1:
                    self.jus[mini] = 1
                else:
                    boo = 1
                    for element in self.real_not_root:
                        if self.unos[element[0]][element[1]][2] == 0:
                            self.belong(element[0], element[1], self.near(element[0], element[1]), 'Fun Justice ')
        for i in range(len(self.jus)):
            self.jus[i] = 0
        
        
        
      ## ФУНКЦИИ ДОПОЛНИТЕЛЬНОЙ ОБРАБОТКИ
    
    
    # СПРАВЕДЛИВОСТЬ УВЕЛИЧИВАЕТ МИНИМАЛЬНУЮ УДОВЛЕТВОРЁННОСТЬ СТРАН ПОСРЕДСТВОМ JUSTICE БОГАТЫЕ ОТДАЮТ БЕДНЫМ
    def justice(self):
        memo = np.array(self.countries)[:, 1].astype(float)
        self.total_justice()
        while ((np.array(self.countries)[:, 1].astype(float) != memo).sum() != 0):
            memo = np.array(self.countries)[:, 1].astype(float)
            self.total_justice()
        
    
    # ОБМЕН ПЫТАЕТСЯ ОБМЕНЯТЬСЯ МЕЖДУ ЛЮБЫМИ ДВУМЯ СТРАНАМИ НЕ УМЕНЬШАЯ УДОВЛЕТВОРЁННОСТЬ НИ ОДНОЙ ИЗ НИХ(n размер кусочков
                                #между которыми будет происходить обмен, рекомендую 16, если ваш компьютер мощнее, можно больше)
    def exchange(self, n = 16):
        k = 0
        for i in range(len(self.countries) - 1):
            for j in range(i + 1, len(self.countries)):
                k += self.exch(i, j, n)
        while k != 0:

            k = 0
            for i in range(len(self.countries) - 1):
                for j in range(i + 1, len(self.countries)):
                    k += self.exch(i, j, n)
        
     
    # КОМБИНАЦИЯ СПРАВЕДЛИВОСТИ И ОБМЕНА (n размер кусочков для функции exchange
                                #между которыми будет происходить обмен, рекомендую 16, если ваш компьютер мощнее, можно больше)
    def just_change(self, n = 16):
        memo = np.array(self.countries)[:, 1].astype(float)
        self.justice()
        self.exchange(n)
        while ((np.array(self.countries)[:, 1].astype(float) != memo).sum() != 0):
            memo = np.array(self.countries)[:, 1].astype(float)
            self.justice()
            self.exchange(n)
    
    
    
      ## ФУНКЦИИ ДЛЯ ВЫВОДОВ
    
    
    # ПИШЕТ ТАБЛИЦУ ЗАВИСТИ ГДЕ СТРАНА ИЗ СТРОКИ ЗАВИДУЕТ СТРАНЕ ИЗ СТОЛБЦА
    def envy_free(self):
        env = [['']]
        for i in range(len(self.countries)):
            env[0].append(self.names[i])
        for i in range(len(self.countries)):
            env.append([self.names[i]])
            for j in range(len(self.countries)):
                env[i + 1].append(self.envy(i, j).astype(int))
        max_len = max([len(str(e)) for r in env for e in r])
        for row in env:
            print(*list(map('{{:>{length}}}'.format(length= max_len).format, row)))
    
    
    # ПИШЕТ ТЕКУЩУЮ УДОВЛЕТВОРЁННОСТЬ СТРАН
    def countries_saty(self):
        sat_c = []
        for i in range(len(self.countries)):
            sat_c.append([self.names[i], self.countries[i][1]])
        max_len = max([len(str(e)) for r in sat_c for e in r])
        for row in sat_c:
            print(*list(map('{{:>{length}}}'.format(length= max_len).format, row)))
    
    
    # ТЕКУЩАЯ КАРТА
    def mapstat(self):
        plt.imshow(np.array(self.unos)[:, :, 2].astype(int), cmap = cm.viridis, 
                   norm = mpl.colors.BoundaryNorm([i for i in range(-1, len(self.countries) + 2)], cm.viridis.N))
        plt.title(str(len(self.anim)) + ' ' + str(np.array(self.countries)[:, 1].astype(int)))
        plt.show()
    
    # АНИМАЦИЯ ИЗМЕНЕНИЯ КАРТЫ необязательно указывать(длительность каждого кадра в милисекундах, ускорение,
                                                                                                           #повторять анимацию?)
    def mapanim(self, interval = 200, x = 1, repeat = False):
        f = plt.figure()
        ax = f.gca()
        im = self.anima.copy()
        image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis, 
                           norm = mpl.colors.BoundaryNorm([i for i in range(-1, len(self.countries) + 2)], cm.viridis.N))
        def function_for_animation(frame_index):
            for i in range(x):
                im[self.anim[min(frame_index * x + i, len(self.anim) - 
                                 1)][0]][self.anim[min(frame_index * x + i, len(self.anim) - 
                                                       1)][1]] = self.anim[min(frame_index * x + i, len(self.anim) - 1)][2]
                image.set_data(im)
            ax.set_title(self.anim[min(frame_index * x, len(self.anim) - 1)][3] 
                         + str(min(frame_index * x, len(self.anim) - 1)) + ' ' 
                         + str(self.anim2[min(frame_index * x, len(self.anim) - 1)]))
        return matplotlib.animation.FuncAnimation(f, function_for_animation, interval=interval, 
                                                  frames=(((len(self.anim) - 1) // x) + 2), repeat = repeat, blit=True)
    
    
    # ГИСТОГРАММА ТЕКУЩЕГО УДОВЛЕТВОРЕНИЯ СТРАН
    def jusstat(self):
        fig = plt.figure(dpi = 80, figsize = (8, 4))
        plt.title(str(len(self.anim2)))
        mpl.rcParams.update({'font.size': 10})
        ax = plt.axes()
        plt.xlim( -0.5, len(self.names) - 0.5)
        for i in range(len(self.names)):
            ax.text(i + 0.15, np.array(self.countries)[:, 1].astype(int)[i], np.array(self.countries)[:, 1].astype(int)[i])
        ax.yaxis.grid(True, zorder = 1)
        plt.bar([x for x in range(len(self.names))], np.array(self.countries)[:, 1].astype(int), width = 0.3, color = 'blue',
                alpha = 0.7, zorder = 2)
        plt.xticks(range(len(self.names)), self.names)
        plt.legend(loc='upper right')
    
    
    # АНИМАЦИЯ ГИСТОГРАММЫ УДОВЛЕТВОРЕНИЯ необязательно(длительность каждого кадра в милисекундах,ускорение,
                                                                                                           #повторять анимацию?)
    def jusanim(self, interval = 200, x = 1, repeat = False):
        fig = plt.figure(dpi = 80, figsize = (8, 4))
        ranges = (np.array(self.anim2).max() - np.array(self.anim2).min()) * 0.1
        def function_for_animation(frame_index):
            plt.title(self.anim[min(frame_index * x, len(self.anim) - 1)][3] + str(min(frame_index * x, len(self.anim) - 1)))
            plt.ylim([np.array(self.anim2).min() - ranges, np.array(self.anim2).max() + ranges])
            plt.xlim( -0.5, len(self.names) - 0.5)
            mpl.rcParams.update({'font.size': 10})
            ax = plt.axes()
            for i in range(len(self.names)):
                ax.text(i + 0.15, self.anim2[min(frame_index * x, len(self.anim) - 1)][i], 
                        self.anim2[min(frame_index * x, len(self.anim) - 1)][i])
            ax.yaxis.grid(True, zorder = 1)
            plt.bar([x for x in range(len(self.names))], self.anim2[min(frame_index * x, len(self.anim) - 1)],
                    width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
            plt.xticks(range(len(self.names)), self.names)
            plt.legend(loc='upper right')
        return matplotlib.animation.FuncAnimation(fig, function_for_animation, interval=interval, repeat = repeat,
                                                  init_func = None,  frames=(((len(self.anim2) - 1) // x) + 2), blit=True)
    
    
    # ТЕКУЩАЯ КАРТА И ГИСТОГРАММА УДОВЛеТВОРеНИЯ СТРАН
    def stat(self):
        nrows = 1
        ncols = 2
        fig = plt.figure(figsize=(10, 5))
        ax = fig.add_subplot(nrows, ncols, 1)
        plt.imshow(np.array(self.unos)[:, :, 2].astype(int))
        plt.title(str(len(self.anim)) + ' ' + str(np.array(self.countries)[:, 1].astype(int)))
        plt.show()
        ax = fig.add_subplot(nrows, ncols, 2)
        plt.title(str(len(self.anim2)))
        mpl.rcParams.update({'font.size': 10})
        plt.xlim( -0.5, len(self.names))
        for i in range(len(self.names)):
            ax.text(i + 0.15, np.array(self.countries)[:, 1].astype(int)[i], np.array(self.countries)[:, 1].astype(int)[i])
        ax.yaxis.grid(True, zorder = 1)
        plt.bar([x for x in range(len(self.names))], np.array(self.countries)[:, 1].astype(int), width = 0.3, color = 'blue',
                alpha = 0.7, zorder = 2)
        plt.xticks(range(len(self.names)), self.names)
        plt.legend(loc='upper right')
    
    
    # АНИМАЦИЯ КАРТЫ И ГИСТОГРАММЫ необязательно (длительность каждого кадра в милисекундах,ускорение, повторять анимацию?)
    def animat(self, interval = 200, x = 1, repeat = False):
        nrows = 1
        ncols = 2
        fig = plt.figure(figsize=(10, 5))
        ranges = (np.array(self.anim2).max() - np.array(self.anim2).min()) * 0.1
        im = self.anima.copy()
        def function_for_animation(frame_index):
            ax = fig.add_subplot(nrows, ncols, 2)
            plt.title(self.anim[min(frame_index * x, len(self.anim) - 1)][3] + str(min(frame_index * x, len(self.anim) - 1)))
            plt.ylim([np.array(self.anim2).min() - ranges, np.array(self.anim2).max() + ranges])
            plt.xlim( -0.5, len(self.names))
            mpl.rcParams.update({'font.size': 10})
            for i in range(len(self.names)):
                ax.text(i + 0.15, self.anim2[min(frame_index * x, len(self.anim) - 1)][i], 
                        self.anim2[min(frame_index * x, len(self.anim) - 1)][i])
            ax.yaxis.grid(True, zorder = 1)
            plt.bar([x for x in range(len(self.names))], self.anim2[min(frame_index * x, len(self.anim) - 1)], 
                    width = 0.3, color = 'blue', alpha = 0.7, zorder = 2)
            plt.xticks(range(len(self.names)), self.names)
            plt.legend(loc='upper right')
            ax = fig.add_subplot(nrows, ncols, 1)
            for i in range(x):
                im[self.anim[min(frame_index * x + i, len(self.anim) - 
                                 1)][0]][self.anim[min(frame_index * x + i, len(self.anim) - 
                                                       1)][1]]= self.anim[min(frame_index * x + i, len(self.anim) - 1)][2]
            image = plt.imshow(im, interpolation='None', animated=True, cmap = cm.viridis, 
                               norm = mpl.colors.BoundaryNorm([i for i in range(-1, len(self.countries) + 2)], cm.viridis.N))
            ax.set_title(self.anim[min(frame_index * x + i, len(self.anim) - 1)][3] + str(min(frame_index * x, 
                                                                                              len(self.anim) - 1)) + ' ' + 
                         str(self.anim2[min(frame_index * x, len(self.anim) - 1)]))
        return matplotlib.animation.FuncAnimation(fig, function_for_animation, interval=interval, repeat = repeat,
                                                  init_func = None,  frames=(((len(self.anim2) - 1) // x) + 2), blit=True)
    
    
    # КАРТА РЕСУРСА (номер ресурса)
    def map_resource(self, n):
        plt.imshow(np.array(self.res_map[n]), cmap = cm.viridis, 
                   norm = mpl.colors.BoundaryNorm([0, 1, 2, 3], cm.viridis.N))
        plt.show()
    
    
    # КАРТА ВСЕХ РЕСУРСОВ ВМЕСТЕ
    def map_all_resources(self):
        arr = self.res_map[0].copy()
        for i in range(len(self.res_map) - 1):
            arr += self.res_map[i + 1]
        plt.imshow(np.array(arr))
        plt.show()
    
    
    # ВСЕ КАРТЫ РЕСУРСОВ
    def map_resources(self):
        f, axarr = plt.subplots(len(self.res_map), 1)
        for i in range(len(self.res_map)):
            axarr[i].imshow(self.res_map[i])
        plt.show()
    
    
    # КАРТА РАССТОЯНИЯ ДЛЯ СТРАНЫ (номер страны)
    def map_dist(self, n):
        plt.imshow(np.array(self.dist_map[n]))
        plt.show()

    
    
    # КАРТА ПОЛЬЗЫ ДЛЯ СТРАНЫ (номер страны)
    def map_saty(self, n):
        plt.imshow(np.array(self.saty_map[n]))
        plt.show()

    
    
    # КАРТА ПОЛЬЗЫ И РАССТОЯНИЯ ДЛЯ СТРАНЫ (номер страны)
    def map_country(self, n):
        f, axarr = plt.subplots(1,2)
        axarr[0].imshow(self.dist_map[n])
        axarr[1].imshow(self.saty_map[n])
        plt.show()
    
    
    # ВСЕ КАРТЫ РАССТОЯНИЙ ДЛЯ СТРАН
    def map_dist_countries(self):
        f, axarr = plt.subplots(len(self.countries), 1)
        for i in range(len(self.countries)):
            axarr[i].imshow(self.dist_map[i])
        plt.show()
    
    
    # ВСЕ КАРТЫ ПОЛЬЗЫ ДЛЯ СТРАН
    def map_saty_countries(self):
        f, axarr = plt.subplots(len(self.countries), 1)
        for i in range(len(self.countries)):
            axarr[i].imshow(self.saty_map[i])
        plt.show()
    
    
    # ВСЕ КАРТЫ ПОЛЬЗ И РАССТОЯНИЙ ДЛЯ СТРАН
    def map_countries(self):
        f, axarr = plt.subplots(len(self.countries), 2)
        for i in range(len(self.countries)):
            axarr[i, 0].imshow(self.dist_map[i])
            axarr[i, 1].imshow(self.saty_map[i])
        plt.show()
    
    
    
      ## СОХРАНЕНИЕ И ЗАГРУЗКА ДАННЫХ ##
        
    
    # СОХРАНИТЬ ТЕРРИТОРИЮ (указать название файла)
    def save(self, name):
        if(self.ije == 1):
            print('')
            self.ije = 0
        sys.stdout.write("Saving...\r".format())
        sys.stdout.flush()
        pd.DataFrame([pd.DataFrame(self.unos), pd.DataFrame(self.countries), pd.DataFrame([self.name]), 
                      pd.DataFrame(self.names), pd.DataFrame(self.jus), pd.DataFrame(self.d), pd.DataFrame(self.anim), 
                      pd.DataFrame(self.anim2), 
                      pd.DataFrame(self.anima), 
                      pd.DataFrame(self.real_not_root), 
                      pd.DataFrame([self.ij]), pd.DataFrame([self.ie])]).to_pickle(name)
        print('Saved!   ')
    
    
    # ЗАГРУЗИТЬ ТЕРРИТОРИЮ (указать название файла)
    def load(self, name):
        if(self.ije == 1):
            print('')
            self.ije = 0

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
        
        self.name = df[0][2][0].values[0]
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.names = df[0][3][0].values.tolist()
        sys.stdout.write("Loading...\r".format())
        sys.stdout.flush()
        
        self.jus = df[0][4][0].values.tolist()
        sys.stdout.write("Loading.  \r".format())
        sys.stdout.flush()
        
        self.d = df[0][5].values.tolist()
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.anim = df[0][6].values.tolist()
        sys.stdout.write("Loading...\r".format())
        sys.stdout.flush()
        
        self.anim2 = df[0][7].values.tolist()
        sys.stdout.write("Loading.  \r".format())
        sys.stdout.flush()
        
        self.anima =df[0][8].values.tolist()
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.res_map = np.zeros((len(self.unos[0][0][0]), len(self.unos), len(self.unos[0])))
        self.dist_map = np.zeros((len(self.countries), len(self.unos), len(self.unos[0]))).tolist()
        self.saty_map = np.zeros((len(self.countries), len(self.unos), len(self.unos[0]))).tolist()
        for i in range(len(self.unos)):
            for j in range(len(self.unos[0])):
                for k in range(len(self.unos[0][0][0])):
                    if self.unos[i][j][2] != -1:
                        self.res_map[k][i][j] += self.unos[i][j][0][k] + 1
                for k in range(len(self.countries)):
                    if self.unos[i][j][2] != -1:
                        if (self.unos[i][j][1] == False) or (self.unos[i][j][2] == k + 1):
                            self.dist_map[k][i][j] = self.unos[i][j][3][k]
                        else:
                            self.dist_map[k][i][j] = -2
                    else:
                        self.dist_map[k][i][j] = -1

                    if self.unos[i][j][2] != -1:
                        if (self.unos[i][j][1] == False) or (self.unos[i][j][2] == k + 1):
                            self.saty_map[k][i][j] = self.unos[i][j][4][k]
                        else:
                            self.saty_map[k][i][j] = -2
                    else:
                        self.saty_map[k][i][j] = -1
        sys.stdout.write("Loading...\r".format())
        sys.stdout.flush()
        
        self.real_not_root = df[0][9].values.tolist()
        sys.stdout.write("Loading. \r".format())
        sys.stdout.flush()
        
        self.ij = df[0][10][0].values[0]
        sys.stdout.write("Loading.. \r".format())
        sys.stdout.flush()
        
        self.ie = df[0][11][0].values[0]
        sys.stdout.write("Loading...\r".format())
        sys.stdout.flush()
    
        print('Loaded!   ')
    
    
    
        ### СИСТЕМНЫЕ ФУНКЦИИ ###(не для вызова и использования, но если аккуратно, то можно)
        
        
        
      ## СТАДНАРТНЫЕ РАССЧЁТЫ И ПРИСВОЕНИЯ ##
    
    
    # РАСЧЁТ РАССТОЯНИЯ ДЛЯ СТРАНЫ (строка участка, столбец участка, номер страны) возвращает минимально расстояние
    def dist(self, f, l, i_coun):
        return np.linalg.norm(np.array(self.countries[i_coun][2] - np.array([f, l])), axis = 1).min()
    
    
    # РАСЧЁТ ПОЛЬЗЫ УЧАСТКА ДЛЯ СТРАНЫ (строка участка, столбец участка, номер страны)возвращает[пользая,
                                                                                                        #минимальное расстояние]
    def saty(self, f, l, i_cun):
        dista = self.dist(f, l, i_cun)
        return max(0, ((np.array(self.unos[f][l][0]) * np.array(self.countries[i_cun][0])).sum() *
                    (self.d[i_cun][1] - dista + 1)) 
                   / (self.d[i_cun][1] - min(dista, self.d[i_cun][0]) + 1)), dista
    
    
    # БЛИЖАЙШАЯ К УЧАСТКУ СТРАНА (строка участка, столбец участка) возвращает номер ближайшей страны
    def near(self, f, l):
        answer = 0
        for i in range(len(self.countries) - 1):
            if ((self.unos[f][l][3][answer] > self.unos[f][l][3][i + 1]) or 
                (self.unos[f][l][3][answer] == self.unos[f][l][3][i + 1] and 
                 ((self.unos[f][l][4][answer] < self.unos[f][l][4][i + 1]) or 
                  ((self.unos[f][l][4][answer] == self.unos[f][l][4][i + 1]) and 
                   (self.countries[answer][1] > self.countries[i+1][1]))))):
                answer = i + 1
        return answer
    
    
    # СТРАНА ДЛЯ КОТОРОЙ УЧАСТОК ПРИНЕСЁТ БОЛЬШЕ ПОЛЬЗЫ (строка участка, столбец участка) возвращает номер страны
    def most_saty(self, f, l):
        answer = 0
        for i in range(len(self.countries) - 1):
            if ((self.unos[f][l][4][answer] < self.unos[f][l][4][i + 1]) or 
            ((self.unos[f][l][4][answer] == self.unos[f][l][4][i + 1]) and 
             ((self.unos[f][l][3][answer] > self.unos[f][l][3][i + 1]) or 
             ((self.unos[f][l][3][answer] == self.unos[f][l][3][i + 1]) and 
              (self.countries[answer][1] > self.countries[i+1][1]))))):
                answer = i+1
        return answer

    
    # ПРИСВОИТЬ УЧАСТОК СТРАНЕ (строка участка, столбец участка, номер сраны)
    def belong(self, f, l, i_cun, func = ''):
        if self.unos[f][l][2] > 0:
            name_i = self.unos[f][l][2]
            self.countries[name_i - 1][1] -= 2 * self.unos[f][l][4][name_i - 1]
            self.countries[name_i - 1][3].remove([f, l])
        self.unos[f][l][2] = i_cun + 1
        self.countries[i_cun][1] += 2 * self.unos[f][l][4][i_cun]
        self.countries[i_cun][3].append([f, l])
        self.anim.append([f, l, i_cun + 1, func])
        self.anim2.append(np.array(self.countries)[:, 1].astype(int).tolist())
        if func == 'Justice ':
            self.ij += 1
            sys.stdout.write("Justice: {0}, exchange: {1} From {2} to {3}                  \r".format(str(self.ij), 
                                                                                                      str(self.ie), 
                                                                                                      self.names[name_i - 1], 
                                                                                                      self.names[i_cun]))
            sys.stdout.flush()
            self.ije = 1
        elif func == 'Exchange ':
            self.ie += 1
            sys.stdout.write("justice: {0}, Exchange: {1} From {2} to {3}                  \r".format(str(self.ij), 
                                                                                                      str(self.ie), 
                                                                                                      self.names[name_i - 1], 
                                                                                                      self.names[i_cun]))
            sys.stdout.flush()
            self.ije = 1
        
        
    
      ## ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ДЛЯ JUSTICE РАБОТАЮЩИЕ С SELF.JUS ##
        
    
    # МИНИМАЛЬНО УДОВЛЕТВРЁННАЯ СТРАНА ИЗ ДОСТУПНЫХ = тех, у которых в self.jus соответсвуещему индексу сопоставлен 0 
    def min_sat(self):
        mini = self.countries[self.jus.index(0)][1]
        answer = self.jus.index(0)
        for i in range(len(self.countries) - 1):
            if self.jus[i+1] == 0 and self.countries[i + 1][1] < mini:
                mini = self.countries[i + 1][1]
                answer = i + 1
        return [mini, answer]
    
    
    # МАКСИМАЛЬНО УДОВЛЕТВОРЁННАЯ СТРАНА ИЗ ДОСТУПНЫХ
    def max_sat(self):
        maxi = self.countries[self.jus.index(0)][1]
        answer = self.jus.index(0)
        for i in range(len(self.countries) - 1):
            if self.jus[i+1] == 0 and self.countries[i + 1][1] > maxi:
                maxi = self.countries[i + 1][1]
                answer = i + 1
        return [maxi, answer]

    
    # МАКСИМАЛЬНО УДОВЛЕТВРЁННАЯ СТРАНА ИЗ НЕДОСТУПНЫХ
    def max_sat_re(self):
        maxi = self.countries[self.jus.index(1)][1]
        answer = self.jus.index(1)
        for i in range(len(self.countries) - 1):
            if self.jus[i + 1] == 1 and self.countries[i + 1][1] > maxi:
                maxi = self.countries[i + 1][1]
                answer = i + 1
        return [maxi, answer]
    
    
    
      ## ВСПОМОГАТЕЛЬНЫЕ ДЛЯ ОБМЕНА И СПРАВЕДЛИВОСТИ
            
 
    # ВЗАИМОВЫГОДНЫЙ ОБМЕН ДВУМЯ УЧАСТКАМИ МЕЖДУ ДВУМЯ СТРАНАМИ (номер первой и второй страны,
    #количество территорий в одном обмене, чем больше, тем дольше будет считаться) возвращает 1 при успехе (иначе 0)
    def exch(self, one, two, num = 16):
        sys.stdout.write("justice: {0}, Exchange: {1} Try from {2} to {3}                \r".format(str(self.ij), 
                                                                                                    str(self.ie), 
                                                                                                    self.names[one], 
                                                                                                    self.names[two],))
        sys.stdout.flush()
        first = []
        second = []
        firstsaty = []
        secondsaty = []
        constraints = []
        for i in range(len(self.countries[one][3])):
            firs = self.countries[one][3][i][0]
            las = self.countries[one][3][i][1]
            if (firs != 0 and (self.unos[firs - 1][las][2] == two + 1)):
                if [firs, las] not in first:
                    first.append([firs, las])
                    firstsaty.append([-self.saty(firs, las, one)[0], self.saty(firs, las, two)[0]])
                if ([firs - 1, las] not in second) and ([firs - 1, las] not in self.countries[two][2]):
                    second.append([firs - 1, las])
                    secondsaty.append([self.saty(firs - 1, las, one)[0], -self.saty(firs - 1, las, two)[0]])
                    if first.count([firs, las]) > 0:   
                        constraints.append([second.index([firs - 1, las]), first.index([firs, las])])
            if (las != 0 and (self.unos[firs][las - 1][2] == two + 1)):
                if [firs, las] not in first:
                    first.append([firs, las])
                    firstsaty.append([-self.saty(firs, las, one)[0], self.saty(firs, las, two)[0]])
                if ([firs, las - 1] not in second) and ([firs, las - 1] not in self.countries[two][2])
                    second.append([firs, las - 1])
                    secondsaty.append([self.saty(firs, las - 1, one)[0], -self.saty(firs, las - 1, two)[0]])
                    if first.count([firs, las]) > 0:
                        constraints.append([second.index([firs, las - 1]), first.index([firs, las])])
            if (las != len(self.unos[0]) - 1 and (self.unos[firs][las + 1][2] == two + 1)):
                if [firs, las] not in first:
                    first.append([firs, las])
                    firstsaty.append([-self.saty(firs, las, one)[0], self.saty(firs, las, two)[0]])
                if ([firs, las + 1] not in second) and ([firs, las + 1] not in self.countries[two][2]):
                    second.append([firs, las + 1])
                    secondsaty.append([self.saty(firs, las + 1, one)[0], -self.saty(firs, las + 1, two)[0]])
                    if first.count([firs, las]) > 0:
                        constraints.append([second.index([firs, las + 1]), first.index([firs, las])])
            if (firs != len(self.unos) - 1 and (self.unos[firs + 1][las][2] == two + 1)):
                if [firs, las] not in first:
                    first.append([firs, las])
                    firstsaty.append([-self.saty(firs, las, one)[0], self.saty(firs, las, two)[0]])
                if ([firs + 1, las] not in second) and ([firs + 1, las] not in self.countries[two][2]):
                    second.append([firs + 1, las])
                    secondsaty.append([self.saty(firs + 1, las, one)[0], -self.saty(firs + 1, las, two)[0]])
                    if first.count([firs, las]) > 0:
                        constraints.append([second.index([firs + 1, las]), first.index([firs, las])])
                    
        for i in range(len(self.countries[one][2])):
            firs = self.countries[one][2][i][0]
            las = self.countries[one][2][i][1]
            if (firs != 0 and (self.unos[firs - 1][las][2] == two + 1)):
                if ([firs - 1, las] not in second) and ([firs - 1, las] not in self.countries[two][2]):
                    second.append([firs - 1, las])
                    secondsaty.append([self.saty(firs - 1, las, one)[0], -self.saty(firs - 1, las, two)[0]])
            if (las != 0 and (self.unos[firs][las - 1][2] == two + 1)):
                if ([firs, las - 1] not in second) and ([firs, las - 1] not in self.countries[two][2]):
                    second.append([firs, las - 1])
                    secondsaty.append([self.saty(firs, las - 1, one)[0], -self.saty(firs, las - 1, two)[0]])
            if (las != len(self.unos[0]) - 1 and (self.unos[firs][las + 1][2] == two + 1)):
                if ([firs, las + 1] not in second) and ([firs, las + 1] not in self.countries[two][2]):
                    second.append([firs, las + 1])
                    secondsaty.append([self.saty(firs, las + 1, one)[0], -self.saty(firs, las + 1, two)[0]])
            if (firs != len(self.unos) - 1 and (self.unos[firs + 1][las][2] == two + 1)):
                if ([firs + 1, las] not in second) and ([firs + 1, las] not in self.countries[two][2]):
                    second.append([firs + 1, las])
                    secondsaty.append([self.saty(firs + 1, las, one)[0], -self.saty(firs + 1, las, two)[0]])
        if (len(first) == 0 or len(second) == 0):
            return 0
        coor = first + second
        saty = firstsaty + secondsaty
        n = ((len(coor) - 1) // num) + 1
        print('\n len', len(coor), 'n', n,'lol \n')
        coor1 = coor.copy()
        k3 = 0
        random.shuffle(coor1)
        coors = []
        for i in range(n - 1):
            coors.append(coor1[i * ((len(coor1) - 1) // n + 1): (i + 1) * ((len(coor1) - 1) // n + 1)])
        coors.append(coor1[(n - 1) * ((len(coor1) - 1) // n + 1):])
        for i in range(n):
            satynew = []
            cons = []
            for elem in coors[i]:
                satynew.append(saty[coor.index(elem)])
            for elem in constraints:
                if coors[i].count(second[elem[0]]) > 0 and coors[i].count(first[elem[1]]) > 0:
                    cons.append([second[elem[0]], first[elem[1]]])
            selection1 = cvxpy.Bool(len(satynew))
            z = cvxpy.Variable()
            constraint1 = [z <= np.array(satynew)[:, 1] * selection1, z <= np.array(satynew)[:, 0] * selection1]
            for elem in cons:
                constraint1.append(selection1[coors[i].index(elem[0])] + selection1[coors[i].index(elem[1])] <= 1)
            
            total_utility1 = z
            my_problem1 = cvxpy.Problem(cvxpy.Maximize(total_utility1), constraint1)
            my_problem1.solve(solver=cvxpy.GLPK_MI)
            first1 = (np.array(satynew)[:, 0] * selection1).value
            second1 = (np.array(satynew)[:, 1] * selection1).value
            if (first1 != 0 or second1 != 0):
                for j in range(len(selection1.value)):
                    if selection1[j].value:
                        if self.unos[coors[i][j][0]][coors[i][j][1]][2] == one + 1:
                            self.belong(coors[i][j][0], coors[i][j][1], two, 'Exchange ')
                        else:
                            self.belong(coors[i][j][0], coors[i][j][1], one, 'Exchange ')
                k3 = 1
        return k3

    
    # ОТДАЁТ САМЫЙ ВЫГОДНЫЙ УЧАСТОК ВТОРОЙ СТРАНЫ ПЕРВОЙ СТРАНЕ (номер первой и второй страны) возвращает индексы участка 
    def justi(self, maxi_i, mini_i):                                                                    # и номер второй страны
        sys.stdout.write("Justice: {0}, exchange: {1} Try from {2} to {3}                  \r".format(str(self.ij), 
                                                                                                      str(self.ie), 
                                                                                                      self.names[maxi_i], 
                                                                                                      self.names[mini_i]))
        ind_max = 0
        maximum = 0
        for i in range(len(self.countries[maxi_i][3])):
            firs = self.countries[maxi_i][3][i][0]
            las = self.countries[maxi_i][3][i][1]
            if (((firs != 0 and (self.unos[firs - 1][las][2] == mini_i + 1)) or
                    (las != 0 and (self.unos[firs][las - 1][2] == mini_i + 1)) or
                    (las != len(self.unos[0]) - 1 and (self.unos[firs][las + 1][2] == mini_i + 1)) or
                    (firs != len(self.unos) - 1 and (self.unos[firs + 1][las][2] == mini_i + 1))) and 
                maximum < (self.unos[self.countries[maxi_i][3][i][0]][self.countries[maxi_i][3][i][1]][4][mini_i] / 
                           (self.unos[self.countries[maxi_i][3][i][0]][self.countries[maxi_i][3][i][1]][4][maxi_i] + 
                            sys.float_info.epsilon))):
                maximum = (self.unos[self.countries[maxi_i][3][i][0]][self.countries[maxi_i][3][i][1]][4][mini_i] / 
                           (self.unos[self.countries[maxi_i][3][i][0]][self.countries[maxi_i][3][i][1]][4][maxi_i] + 
                            sys.float_info.epsilon))
                ind_max = i + 1
        if (ind_max != 0):
            before = [self.countries[maxi_i][3][ind_max - 1][0], self.countries[maxi_i][3][ind_max - 1][1]]
            self.belong(before[0], before[1], mini_i, 'Justice ')
            return [before[0] + 1, before[1] + 1, maxi_i]
        return [0, 0, maxi_i]
    
    
    # ОТ САМОЙ БОГАТОЙ СТРАНЕ ОТДАЁТ БЕДНОЙ С ОМОЩЬЮ JUSTICE
    def one_justice(self):
        min0 = self.min_sat()[0]
        min1 = self.min_sat()[1]
        max0 = self.max_sat()[0]
        max1 = self.max_sat()[1]
        before = self.justi(max1, min1)
        while ((min0 < self.countries[max1][1] or
             (min0 == self.countries[max1][1] and
              max0 < self.countries[min1][1])) and before[:2] != [0, 0]):
            min0 = self.min_sat()[0]
            min1 = self.min_sat()[1]
            max0 = self.max_sat()[0]
            max1 = self.max_sat()[1]
            before = self.justi(max1, min1)
        if (before[:2] != [0, 0]):
            self.belong(before[0] - 1, before[1] - 1, before[2], 'Justice ')
    
    
    # ОТ ВСЕХ СТРАН ОТДАЁТ САМОЙ БЕДНОЙ
    def all_justice(self):
        self.one_justice()
        self.jus[self.max_sat()[1]] = 1
        if self.jus.count(0) > 1:
            self.all_justice()
        self.jus[self.max_sat_re()[1]] = 0
    
    
    # ОТ ВСЕХ СТРАН ОТДАЁТ ВСЕМ(БОГАТЕЙШИЕ БЕДНЕЙШИМ)
    def total_justice(self):
        self.all_justice()
        self.jus[self.min_sat()[1]] = 1
        if self.jus.count(0) > 1:
            self.total_justice()
        else:
            for i in range(len(self.jus)):
                self.jus[i] = 0
    
    
      ## ВСПОМОГАТЕЛНЫЕ ФУНКЦИИ ДЛЯ ВЫВОДОВ
        
    
    # ЗАВИСТЬ ПЕРВОЙ СТРАНЫ ВТОРОЙ СТРАНЕ (номер первой страны, номер второй страны)
    def envy(self, coun_1, coun_2): 
        mini = 0
        for i in range(len(self.countries[coun_1][3])):
            mini += self.unos[self.countries[coun_1][3][i][0]][self.countries[coun_1][3][i][1]][4][coun_1]
        for i in range(len(self.countries[coun_2][3])):
            mini -= self.unos[self.countries[coun_2][3][i][0]][self.countries[coun_2][3][i][1]][4][coun_1]
        return mini
