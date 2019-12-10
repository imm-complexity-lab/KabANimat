import pygame
import random
from collections import deque
from copy import deepcopy
import matplotlib.pyplot as plt
from time import sleep
import math
import numpy as np
import re
import xlsxwriter as xl
import csv

#############################
# дисплейные константы
const_screen_size = 700
const_map_size = 100
const_rect_size = int(const_screen_size / const_map_size)
const_brush_num = 5 # число кисточек, которые двигаются независимо при отрисовке карты (лоскутчатость)

const_draw_map_switch = False # отрисовывать ли ход эксперимента
const_draw_graphs_switch = False # рисовать ли графики по окончании
const_xlsx_switch = False # писать ли каждый эксперимент в эксель

if const_draw_map_switch: map_to_display = pygame.display.set_mode((const_screen_size, const_screen_size))

const_color_bad = (160,82,45)
const_color_normal = (210,180,140)
const_color_good = (60,179,113)

#############################
# средние энергии клеток каждого типа
# фактические будут выданы случайно в интервале +-10 от средних
const_bad_init_cell_energy = 20
const_normal_init_cell_energy = 50
const_good_init_cell_energy = 90


#############################
# основные константы (их можно и нужно варьировать)
const_memory_size = 10 # сколько клеточек назад кабан помнит (длина серого хвостика)
const_energy_for_move = const_normal_init_cell_energy/2 # энергия, затрачиваемая на один ход (сейчас равна среднему
                                                      # значению питательности клетки в лучшее из времен года
const_energy_for_stay = const_energy_for_move/2 # если не идем, то тратим в 2 раза меньше энергии
const_initial_energy = const_energy_for_move * 10 # начальная энергия (сейчас такая, чтобы кабан мог сделать 20 шагов
                                                  # вообще без всякой подпитки, наука биология подсказывает, что
                                                  # не больше 20)


const_winter_hardness = 3 # во сколько раз качество каждой клетки будет уменьшено к середине зимы
                          # (уменьшающий коэффициент стартует с 1 и двигается до данного значения, а потом обратно к 1
                          # по формуле, в основе которой синус)


const_dream = 10000 # значение мечты: чем больше, тем дольше кабан будет мчаться за мечтой, не обращая внимание на
                    # синиц в руках

const_experiment_length = 1000 # число шагов в эксперименте, может быть любым, но маленькое -- плохо, т.к. кабан не
                               # успевает разведать местность

const_num_of_animats = 100 # число аниматов

const_map_proportions = (0.4,0.6,0.0) # пропорции в которых создаются bad/normal/good клетки на карте (сумма должна быть примерно 1)

const_experiment_speed = 100 # 10 -- для визуального, 1000 -- для быстрого эксперимента


# какие стратегии будем сравнивать (бывают: 'random', 'random_with_memory', 'greedy', 'greedy_with_memory',
#                                           'dreamer', 'dreamer_with_memory','dreamer_greedy', 'dreamer_greedy_with_memory'
#strategies = ['random_with_memory','greedy_with_memory', 'dreamer_with_memory']
#strategies = ['levy_random(mu=2,a=3.14)','levy_dreamer(mu=2,a=3.14)','random']
#strategies = ['levy_dreamer(mu=2,a=3.14)','random']



### ОБЛАСТЬ БОЛЬШОГО ЭКСПЕРИМЕНТА
const_num_of_repetitions = 3 # число повторений при равных условиях эксперимента (генерятся только новые карты)
strategies = ['greedy_with_memory','levy_greedy(mu=2,a=3.14)','levy_dreamer(mu=2,a=3.14)'] # стратегии, которые будем рассматривать в большом эксперименте
#maps = [(0.67,0.3,0.03)] # качества карт, которые будем рассматривать в большом эксперименте
maps = [(0,1,0)] # качества карт, которые будем рассматривать в большом эксперименте
winters = [1,4,16] # суровости зим, которые будем рассматривать в большом эксперименте


### ПАРАМЕТРЫ ПОЛЕТА ЛЕВИ
const_levy_flight_param_mu = 2.0 # параметр мю из стратегии движения леви-флайт по умолчанию
const_levy_flight_conus_width = math.pi # ширирна конуса с медианой из предыдущего направления,
                                        # из которого равновероятно выбирается следующее направление по умолчанию





# класс анимата -- все, что связано с ним
class randomly_moving_kaban():

    def __init__(self, surface = None, map = None, map_position=[0,0], color = (0,0,0)):

        self.kvadr = pygame.rect.Rect((map_position[0] * const_rect_size,
                                      map_position[1] * const_rect_size,
                                      const_rect_size,
                                      const_rect_size))

        self.surface = surface
        self.pos = map_position
        self.memory = deque([map_position for i in range(const_memory_size)],const_memory_size)
        self.energy = const_initial_energy
        self.color = color
        self.color_dop = color
        self.map = map
        self.step = 1
        self.dreamer_greedy_switch = 'dreamer'
        self.alive = True
        self.levy_angle = random.uniform(0,2*math.pi)
        self.levy_distance = 0
        self.real_pos = deepcopy(map_position)
        self.step_x = 0
        self.step_y = 0
        self.init_pos = deepcopy(map_position)


    # единая функция move для всех случаев
    def live_one_day(self,strategy='random'):

        where = [0,0]

        # выбираем направление в зависимости от выбранной стратегии
        if strategy == 'random':
            self.color = (0, 0, 0)
            where = self.move_random()
        if strategy == 'random_with_memory':
            self.color = (0, 0, 0)
            where = self.move_random_with_memory()
        if strategy == 'greedy':
            self.color = (255, 0, 0)
            where = self.move_greedy()
        if strategy == 'greedy_with_memory':
            self.color = (255, 0, 0)
            where = self.move_greedy_with_memory()
        if strategy == 'dreamer':
            self.color = (0, 0, 255)
            where = self.move_dreamer()
        if strategy == 'dreamer_with_memory':
            self.color = (0, 0, 255)
            where = self.move_dreamer_with_memory()
        if strategy == 'dreamer_greedy':
            self.color = (0, 0, 255) # но позже он переключится на красный, когда кабан станет жадиной
            where = self.move_dreamer_greedy()
        if strategy == 'dreamer_greedy_with_memory':
            self.color = (0, 0, 255) # но позже он переключится на красный, когда кабан станет жадиной
            where = self.move_dreamer_greedy_with_memory()

        match = re.match('levy_random\(\s*mu\s*=\s*([\d\.]+)\s*,\s*a\s*=\s*([\d\.]+)\s*\)',strategy)
        if match:
            self.color = (102, 0, 153)
            self.color_dop = (0,0,0)
            where = self.levy_random(mu=float(match.group(1)),con=float(match.group(2)))

        match = re.match('levy_dreamer\(\s*mu\s*=\s*([\d\.]+)\s*,\s*a\s*=\s*([\d\.]+)\s*\)',strategy)
        if match:
            self.color = (102, 0, 153)
            self.color_dop = (0,0,255)
            where = self.levy_dreamer(mu=float(match.group(1)),con=float(match.group(2)))

        match = re.match('levy_greedy\(\s*mu\s*=\s*([\d\.]+)\s*,\s*a\s*=\s*([\d\.]+)\s*\)',strategy)
        if match:
            self.color = (102, 0, 153)
            self.color_dop = (255,0,0)
            where = self.levy_greedy(mu=float(match.group(1)),con=float(match.group(2)))

        # делаем шаг
        self.pos[0] += where[0]
        self.pos[1] += where[1]
        if const_draw_map_switch:
            self.kvadr.move_ip(const_rect_size * where[0], const_rect_size * where[1])


        # тратим энергию
        if where != [0,0]: self.energy -= const_energy_for_move # если сделан шаг
        if where == [0,0]: self.energy -= const_energy_for_stay # если остались на месте


        # приобретаем энергию
        self.energy += self.map.cells[self.pos[0]][self.pos[1]].quality


        # если рисуем
        if const_draw_map_switch:

            # отрисовываем тень шагов истории
            for pos in self.memory:
                r = pygame.rect.Rect((pos[0] * const_rect_size,
                                  pos[1] * const_rect_size,
                                  const_rect_size,
                                  const_rect_size))
                pygame.draw.rect(self.surface, (200, 200, 200), r)

            # отрисовываем сделанный шаг
            pygame.draw.rect(self.surface, self.color, self.kvadr)


    def levy_greedy(self,mu=const_levy_flight_param_mu,con=const_levy_flight_conus_width):

        # если дистанция исчерпалась и пора выбирать новое направление
        if self.levy_distance == 0:

            # выбираем новое направление (примерно в том же секторе +- pi/2
            self.levy_angle = random.uniform(self.levy_angle-con/2,
                                             self.levy_angle+con/2)


            # выбираем новое число шагов (от 1 до полэкрана)
            part_sum = 0
            for i in range(1,int(const_map_size/2)): part_sum += 1/i**mu
            probabilities = [(1/i**mu)/part_sum for i in range(1,int(const_map_size/2))]
            self.levy_distance = np.random.choice(range(1,int(const_map_size/2)),p=probabilities)



            # функция вернет +1 или -1 в зависимости от знака а
            sign = lambda a: (a > 0) - (a < 0)

            # определяем новый сдвиг по х и по у
            if abs(math.cos(self.levy_angle))>abs(math.sin(self.levy_angle)):
                self.step_x = sign(math.cos(self.levy_angle))
                self.step_y = math.tan(self.levy_angle)
            if abs(math.cos(self.levy_angle))<abs(math.sin(self.levy_angle)):
                self.step_y = sign(math.sin(self.levy_angle))
                self.step_x = math.cos(self.levy_angle)/math.sin(self.levy_angle)
            if abs(math.cos(self.levy_angle))==abs(math.sin(self.levy_angle)):
                self.step_x = sign(math.cos(self.levy_angle))
                self.step_y = sign(math.sin(self.levy_angle))



        # если дистанция еще не исчерпалась, но мы уже у края и хотим шагнуть за него, то исчерпываем дистанцию
        if self.levy_distance > 0:
            if (self.pos[0] == 0 and self.step_x < 0) or \
               (self.pos[0] == const_map_size-1 and self.step_x > 0) or \
               (self.pos[1] == 0 and self.step_y < 0) or \
               (self.pos[1] == const_map_size - 1 and self.step_y > 0):
               self.levy_distance = 0



        where = [0,0]
        # если дистанция еще не исчерпалась, и мы уже прошли проверку на край, то
        if self.levy_distance > 0:

            where[0] = int(int(self.real_pos[0] + self.step_x + 0.5) - self.pos[0] + 0.5)
            where[1] = int(int(self.real_pos[1] + self.step_y + 0.5) - self.pos[1] + 0.5)

            # если следующий шаг не выведет нас из области текущего качества, то делаем его
            if self.map.cells[self.pos[0] + where[0]][self.pos[1] + where[1]].num_type >= \
                    self.map.cells[self.pos[0]][self.pos[1]].num_type:

                self.real_pos[0] += self.step_x
                self.real_pos[1] += self.step_y

                self.levy_distance -= 1

            # если следующий шаг приведет в область хуже, то не делаем
            else:

                where = [0,0]
                self.levy_distance = 0

        return where


    def levy_random(self,mu=const_levy_flight_param_mu,con=const_levy_flight_conus_width):

        # если дистанция исчерпалась и пора выбирать новое направление
        if self.levy_distance == 0:

            # выбираем новое направление (примерно в том же секторе +- pi/2
            self.levy_angle = random.uniform(self.levy_angle-con/2,
                                             self.levy_angle+con/2)


            # выбираем новое число шагов (от 1 до полэкрана)
            part_sum = 0
            for i in range(1,int(const_map_size/2)): part_sum += 1/i**mu
            probabilities = [(1/i**mu)/part_sum for i in range(1,int(const_map_size/2))]
            self.levy_distance = np.random.choice(range(1,int(const_map_size/2)),p=probabilities)



            # функция вернет +1 или -1 в зависимости от знака а
            sign = lambda a: (a > 0) - (a < 0)

            # определяем новый сдвиг по х и по у
            if abs(math.cos(self.levy_angle))>abs(math.sin(self.levy_angle)):
                self.step_x = sign(math.cos(self.levy_angle))
                self.step_y = math.tan(self.levy_angle)
            if abs(math.cos(self.levy_angle))<abs(math.sin(self.levy_angle)):
                self.step_y = sign(math.sin(self.levy_angle))
                self.step_x = math.cos(self.levy_angle)/math.sin(self.levy_angle)
            if abs(math.cos(self.levy_angle))==abs(math.sin(self.levy_angle)):
                self.step_x = sign(math.cos(self.levy_angle))
                self.step_y = sign(math.sin(self.levy_angle))



        # если дистанция еще не исчерпалась, но мы уже у края и хотим шагнуть за него, то исчерпываем дистанцию
        if self.levy_distance > 0:
            if (self.pos[0] == 0 and self.step_x < 0) or \
               (self.pos[0] == const_map_size-1 and self.step_x > 0) or \
               (self.pos[1] == 0 and self.step_y < 0) or \
               (self.pos[1] == const_map_size - 1 and self.step_y > 0):
               self.levy_distance = 0



        where = [0,0]
        # если дистанция еще не исчерпалась, и мы уже прошли проверку на край, то
        if self.levy_distance > 0:

            self.real_pos[0] += self.step_x
            self.real_pos[1] += self.step_y
            where[0] = int(int(self.real_pos[0] + 0.5) - self.pos[0] + 0.5)
            where[1] = int(int(self.real_pos[1] + 0.5) - self.pos[1] + 0.5)


            self.levy_distance -= 1

        return where


    def levy_dreamer(self,mu=const_levy_flight_param_mu,con=const_levy_flight_conus_width):


        # если сила мечты перевешивает, идем дальше
        if self.dream_expectation(self.step) * const_dream >= self.map.cells[self.pos[0]][self.pos[1]].quality:

            # если дистанция исчерпалась и пора выбирать новое направление
            if self.levy_distance == 0:

                # выбираем новое направление (примерно в том же секторе +- pi/2
                self.levy_angle = random.uniform(self.levy_angle-con/2,
                                                 self.levy_angle+con/2)


                # выбираем новое число шагов (от 1 до полэкрана)
                part_sum = 0
                for i in range(1,int(const_map_size/2)): part_sum += 1/i**mu
                probabilities = [(1/i**mu)/part_sum for i in range(1,int(const_map_size/2))]
                self.levy_distance = np.random.choice(range(1,int(const_map_size/2)),p=probabilities)



                # функция вернет +1 или -1 в зависимости от знака а
                sign = lambda a: (a > 0) - (a < 0)

                if abs(math.cos(self.levy_angle))>abs(math.sin(self.levy_angle)):
                    self.step_x = sign(math.cos(self.levy_angle))
                    self.step_y = math.tan(self.levy_angle)
                if abs(math.cos(self.levy_angle))<abs(math.sin(self.levy_angle)):
                    self.step_y = sign(math.sin(self.levy_angle))
                    self.step_x = math.cos(self.levy_angle)/math.sin(self.levy_angle)
                if abs(math.cos(self.levy_angle))==abs(math.sin(self.levy_angle)):
                    self.step_x = sign(math.cos(self.levy_angle))
                    self.step_y = sign(math.sin(self.levy_angle))



            # если дистанция еще не исчерпалась, но мы уже у края, то исчерпываем дистанцию
            if self.levy_distance > 0:
                if (self.pos[0] == 0 and self.step_x < 0) or \
                   (self.pos[0] == const_map_size-1 and self.step_x > 0) or \
                   (self.pos[1] == 0 and self.step_y < 0) or \
                   (self.pos[1] == const_map_size - 1 and self.step_y > 0):
                   self.levy_distance = 0



            where = [0,0]
            # если дистанция еще не исчерпалась, и мы уже прошли проверку на край, то
            if self.levy_distance > 0:

                self.real_pos[0] += self.step_x
                self.real_pos[1] += self.step_y
                where[0] = int(int(self.real_pos[0] + 0.5) - self.pos[0] + 0.5)
                where[1] = int(int(self.real_pos[1] + 0.5) - self.pos[1] + 0.5)


                self.levy_distance -= 1

                # считаем сделанные шаги (для дримера)
                self.step += 1

            return where

        # если мечта исчерпалась, стоим (если качество текущей клетки не меняется, то вечно, иначе может быть
        # качество станет таким плохим, что кабан снова захочет пойти)
        else: return [0,0]


    def move_random_with_memory(self):

        # базовые ходы -- вверх, вправо, вниз, влево
        base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

        # отбрасываем некоторые варианты, если мы у границы
        if self.pos[0] == 0: base_moves.remove([-1,0])
        if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
        if self.pos[1] == 0: base_moves.remove([0,-1])
        if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

        # убираем из возможных ходов те, что есть в памяти
        for new_pos in list(self.memory):
            delta = [new_pos[0] - self.pos[0],new_pos[1] - self.pos[1]]
            if delta in base_moves: base_moves.remove(delta)


        # если есть куда идти, выбираем куда шагать
        if len(base_moves) > 0: where = random.choice(base_moves)
        # иначе стоим на месте
        else: where=[0,0]

        # добавляем новую позицию (или старую) в память в начало
        self.memory.appendleft([self.pos[0]+where[0],self.pos[1]+where[1]])

        return where


    def move_random(self):

        # базовые ходы -- вверх, вправо, вниз, влево
        base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

        # отбрасываем некоторые варианты, если мы у границы
        if self.pos[0] == 0: base_moves.remove([-1,0])
        if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
        if self.pos[1] == 0: base_moves.remove([0,-1])
        if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

        # выбираем куда шагать
        return random.choice(base_moves)


    def move_greedy(self):

        # базовые ходы -- вверх, вправо, вниз, влево
        base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

        # отбрасываем некоторые варианты, если мы у границы
        if self.pos[0] == 0: base_moves.remove([-1,0])
        if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
        if self.pos[1] == 0: base_moves.remove([0,-1])
        if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

        # убираем из возможных ходов те, что приводят в клетку хуже по качеству
        qualitative_base_moves = []
        for move in base_moves:
            if self.map.cells[self.pos[0]+move[0]][self.pos[1]+move[1]].num_type >= \
               self.map.cells[self.pos[0]][self.pos[1]].num_type:
                qualitative_base_moves.append(move)

        # выбираем куда шагать
        if len(qualitative_base_moves)>0:
            return random.choice(qualitative_base_moves)
        else:
            return [0,0]


    def move_greedy_with_memory(self):

        # базовые ходы -- вверх, вправо, вниз, влево
        base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

        # отбрасываем некоторые варианты, если мы у границы
        if self.pos[0] == 0: base_moves.remove([-1,0])
        if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
        if self.pos[1] == 0: base_moves.remove([0,-1])
        if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

        # убираем из возможных ходов те, что есть в памяти
        for new_pos in list(self.memory):
            delta = [new_pos[0] - self.pos[0],new_pos[1] - self.pos[1]]
            if delta in base_moves: base_moves.remove(delta)

        # убираем из возможных ходов те, что приводят в клетку хуже по качеству
        qualitative_base_moves = []
        for move in base_moves:
            if self.map.cells[self.pos[0]+move[0]][self.pos[1]+move[1]].num_type >= \
               self.map.cells[self.pos[0]][self.pos[1]].num_type:
                qualitative_base_moves.append(move)

        # если есть куда идти, выбираем куда шагать
        if len(qualitative_base_moves) > 0: where = random.choice(qualitative_base_moves)
        # иначе стоим на месте
        else: where=[0,0]

        # добавляем новую позицию (или старую) в память в начало
        self.memory.appendleft([self.pos[0]+where[0],self.pos[1]+where[1]])

        return where


    # служебная функция для расчета остановки дримера
    def dream_expectation(self,step):

        if step == 1: return 1
        if step == 2: return 1/2
        if step >= 3:
            return 1-sum([1/(n*(n+1)) for n in range(1,step+1)])


    def move_dreamer(self):

        # если сила мечты перевешивает, идем дальше
        if self.dream_expectation(self.step) * const_dream >= self.map.cells[self.pos[0]][self.pos[1]].quality:

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1,0])
            if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0,-1])
            if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

            # выбираем куда шагать
            if len(base_moves)>0:

                # считаем сделанные шаги (для дримера)
                self.step += 1

                return random.choice(base_moves)

            else: return [0,0]

        # если мечта исчерпалась, стоим (если качество текущей клетки не меняется, то вечно, иначе может быть
        # качество станет таким плохим, что кабан снова захочет пойти)
        else: return [0,0]


    def move_dreamer_with_memory(self):

        # если сила мечты перевешивает, идем дальше
        if self.dream_expectation(self.step) * const_dream >= self.map.cells[self.pos[0]][self.pos[1]].quality:

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1,0])
            if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0,-1])
            if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

            # убираем из возможных ходов те, что есть в памяти
            for new_pos in list(self.memory):
                delta = [new_pos[0] - self.pos[0], new_pos[1] - self.pos[1]]
                if delta in base_moves: base_moves.remove(delta)

            # если есть куда идти, выбираем куда шагать
            if len(base_moves) > 0:

                # считаем сделанные шаги (для дримера)
                self.step += 1

                where = random.choice(base_moves)

            # иначе стоим на месте
            else:
                where = [0, 0]

            # добавляем новую позицию (или старую) в память в начало
            self.memory.appendleft([self.pos[0] + where[0], self.pos[1] + where[1]])

            return where


        # если мечта исчерпалась, стоим (если качество текущей клетки не меняется, то вечно, иначе может быть
        # качество станет таким плохим, что кабан снова захочет пойти)
        else: return [0,0]


    def move_dreamer_greedy(self):

        # если у нас еще режим дримера и сила мечты перевешивает, идем дальше
        if self.dreamer_greedy_switch == 'dreamer' and \
                self.dream_expectation(self.step) * const_dream >= self.map.cells[self.pos[0]][self.pos[1]].quality:

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1,0])
            if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0,-1])
            if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

            # выбираем куда шагать
            if len(base_moves)>0:

                # считаем сделанные шаги (для дримера)
                self.step += 1

                return random.choice(base_moves)

            else: return [0,0]

        # если мечта исчерпалась, включаем жадину
        else:

            # переключаемся в режим жадины
            self.dreamer_greedy_switch = 'greedy'
            self.color = (255,0,0)

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1, 0], [-1, 0], [0, 1], [0, -1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1, 0])
            if self.pos[0] == const_map_size - 1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0, -1])
            if self.pos[1] == const_map_size - 1: base_moves.remove([0, 1])

            # убираем из возможных ходов те, что приводят в клетку хуже по качеству
            qualitative_base_moves = []
            for move in base_moves:
                if self.map.cells[self.pos[0] + move[0]][self.pos[1] + move[1]].num_type >= \
                        self.map.cells[self.pos[0]][self.pos[1]].num_type:
                    qualitative_base_moves.append(move)

            # выбираем куда шагать
            if len(qualitative_base_moves) > 0:
                return random.choice(qualitative_base_moves)
            else:
                return [0, 0]


    def move_dreamer_greedy_with_memory(self):

        # если у нас еще режим дримера и сила мечты перевешивает, идем дальше
        if self.dreamer_greedy_switch == 'dreamer' and \
                self.dream_expectation(self.step) * const_dream >= self.map.cells[self.pos[0]][self.pos[1]].quality:

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1,0],[-1,0],[0,1],[0,-1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1,0])
            if self.pos[0] == const_map_size-1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0,-1])
            if self.pos[1] == const_map_size-1: base_moves.remove([0, 1])

            # убираем из возможных ходов те, что есть в памяти
            for new_pos in list(self.memory):
                delta = [new_pos[0] - self.pos[0], new_pos[1] - self.pos[1]]
                if delta in base_moves: base_moves.remove(delta)

            # если есть куда идти, выбираем куда шагать
            if len(base_moves) > 0:

                # считаем сделанные шаги (для дримера)
                self.step += 1

                where = random.choice(base_moves)

            # иначе стоим на месте
            else:
                where = [0, 0]

            # добавляем новую позицию (или старую) в память в начало
            self.memory.appendleft([self.pos[0] + where[0], self.pos[1] + where[1]])

            return where

        # если мечта исчерпалась, включаем жадину
        else:

            # переключаемся в режим жадины
            self.dreamer_greedy_switch = 'greedy'
            self.color = (255,0,0)

            # базовые ходы -- вверх, вправо, вниз, влево
            base_moves = [[1, 0], [-1, 0], [0, 1], [0, -1]]

            # отбрасываем некоторые варианты, если мы у границы
            if self.pos[0] == 0: base_moves.remove([-1, 0])
            if self.pos[0] == const_map_size - 1: base_moves.remove([1, 0])
            if self.pos[1] == 0: base_moves.remove([0, -1])
            if self.pos[1] == const_map_size - 1: base_moves.remove([0, 1])

            # убираем из возможных ходов те, что есть в памяти
            for new_pos in list(self.memory):
                delta = [new_pos[0] - self.pos[0], new_pos[1] - self.pos[1]]
                if delta in base_moves: base_moves.remove(delta)

            # убираем из возможных ходов те, что приводят в клетку хуже по качеству
            qualitative_base_moves = []
            for move in base_moves:
                if self.map.cells[self.pos[0] + move[0]][self.pos[1] + move[1]].num_type >= \
                        self.map.cells[self.pos[0]][self.pos[1]].num_type:
                    qualitative_base_moves.append(move)

            # если есть куда идти, выбираем куда шагать
            if len(qualitative_base_moves) > 0:
                where = random.choice(qualitative_base_moves)
            # иначе стоим на месте
            else:
                where = [0, 0]

            # добавляем новую позицию (или старую) в память в начало
            self.memory.appendleft([self.pos[0] + where[0], self.pos[1] + where[1]])

            return where


# класс клетки карты
class cell():

    def __init__(self,type='normal'):
        self.type = type
        if self.type == 'bad':
            self.quality = random.randint(1, 20)
            self.color = const_color_bad
            self.num_type = 0
        if self.type == 'normal':
            self.quality = random.randint(40, 60)
            self.color = const_color_normal
            self.num_type = 1
        if self.type == 'good':
            self.quality = random.randint(80, 100)
            self.color = const_color_good
            self.num_type = 2

# класс кисточки (для генерации карты)
class brush():

    def __init__(self,map,x_start,y_start):
        self.x=x_start
        self.y=y_start
        self.map = map

    def move_random(self):

        where = random.choice([1,2,3,4])

        if where == 1 and self.x > 0: self.x -= 1
        if where == 2 and self.x < self.map.size-1: self.x += 1
        if where == 3 and self.y > 0: self.y -= 1
        if where == 4 and self.y < self.map.size-1: self.y += 1

class map():

    def __init__(self,bad_normal_good = (0.33,0.33,0.33), brush_num = const_brush_num, surface = None):

        self.surface = surface
        self.size = const_map_size

        # изначально красим все клетки в плохой цвет
        self.cells = [[cell(type='bad') for j in range(self.size)] for i in range(self.size)]

        # создаем набор кисточек
        brushes = [brush(map=self,
                         x_start=random.randint(1,self.size-1),
                         y_start=random.randint(1,self.size-1))
                   for i in range(brush_num)]


        # генерация карты с пропорционально заданными областями
        ok = True
        painted_cells = 0
        base_type = 'bad'
        new_type = 'normal'
        while ok:
            for br in brushes:
                if self.cells[br.x][br.y].type == base_type:
                    self.cells[br.x][br.y] = cell(type=new_type)
                    painted_cells += 1
                    if base_type == 'bad' and painted_cells/(self.size**2) >= bad_normal_good[1]+bad_normal_good[2]:
                        base_type = 'normal'
                        new_type = 'good'
                        painted_cells = 0
                    if base_type == 'normal' and painted_cells/(self.size**2) >= bad_normal_good[2]:
                        ok = False

                        # проверка верности пропорций площадей сгенерированных страт
                        x, y, z = 0, 0, 0
                        for i in range(self.size):
                            for j in range(self.size):
                                if self.cells[i][j].type == 'bad': x += 1
                                if self.cells[i][j].type == 'normal': y += 1
                                if self.cells[i][j].type == 'good': z += 1
                        print('Real map proportion:', x / self.size ** 2, y / self.size ** 2, z / self.size ** 2)

                        break
                br.move_random()

        # запасной вариант изначальной карты
        self.cells_initial = deepcopy(self.cells)

        # отрисовка сгенерированной карты на слой self.surface (background)
        if const_draw_map_switch:
            for i in range(self.size):
                for j in range(self.size):
                    pygame.draw.rect(self.surface,
                                     self.cells[i][j].color,
                                     pygame.rect.Rect((i * const_rect_size, j * const_rect_size, const_rect_size , const_rect_size)))

# отрисовка графиков, накопленных в logs
def write_xlsx_draw_graphs(logs):

    # подготовим наборы средних значений
    for strategy in strategies:
        for iteration in range(const_experiment_length):

            # рассчитываем средние значения для логов на этом шаге
            if logs[strategy]['population_abundance'][iteration] > 0:
                logs[strategy]['population_average_dispersal'][iteration] = logs[strategy]['population_dispersal'][iteration] / \
                                                                            logs[strategy]['population_abundance'][iteration]
                logs[strategy]['population_average_energy'][iteration] = logs[strategy]['population_energy'][iteration] / \
                                                                         logs[strategy]['population_abundance'][iteration]
                logs[strategy]['average_cells_quality'][iteration] = logs[strategy]['cells_quality'][iteration] / \
                                                                     logs[strategy]['population_abundance'][iteration]
                logs[strategy]['average_energy_and_quality'][iteration] = logs[strategy]['population_energy_and_quality'][iteration] / \
                                                                     logs[strategy]['population_abundance'][iteration]
            else:
                logs[strategy]['population_average_dispersal'][iteration] = 0
                logs[strategy]['population_average_energy'][iteration] = 0
                logs[strategy]['average_cells_quality'][iteration] = 0
                logs[strategy]['average_energy_and_quality'][iteration] = 0

    # экспорт сырых данных в эксель
    if const_xlsx_switch:
        workbook = xl.Workbook('KabANimats.xlsx')
        i = 0
        worksheets = []
        for strategy in strategies:
            worksheets.append(workbook.add_worksheet(strategy))
            worksheets[-1].write_column(row=0, col=0, data = ['Iteration']+list(range(const_experiment_length)))
            worksheets[-1].write_column(row=0, col=1, data = ['Abundance']+logs[strategy]['population_abundance'])
            worksheets[-1].write_column(row=0, col=2, data = ['Total Energy'] + logs[strategy]['population_energy'])
            worksheets[-1].write_column(row=0, col=3, data = ['Average Energy'] + logs[strategy]['population_average_energy'])
            worksheets[-1].write_column(row=0, col=4, data = ['Total Cells Quality'] + logs[strategy]['cells_quality'])
            worksheets[-1].write_column(row=0, col=5, data=['Average Cells Quality'] + logs[strategy]['average_cells_quality'])
            worksheets[-1].write_column(row=0, col=6, data = ['Total Energy*Quality'] + logs[strategy]['population_energy_and_quality'])
            worksheets[-1].write_column(row=0, col=7,
                                        data=['Average Energy*Quality'] + logs[strategy]['average_energy_and_quality'])
            worksheets[-1].write_column(row=0, col=8,
                        data=['Total Dispersal'] + logs[strategy]['population_dispersal'])
            worksheets[-1].write_column(row=0, col=9,
                        data=['Average Dispersal'] + logs[strategy]['population_average_dispersal'])
            # worksheets[-1].write_column(row=0, col=6,
            #             data=['Average Energy'] + logs[strategy]['population_average_energy'])
            # worksheets[-1].write_column(row=0, col=6,
            #             data=['Average Energy'] + logs[strategy]['population_average_energy'])
            # worksheets[-1].write_column(row=0, col=7,
            #             data=['Average Cell Quality'] + logs[strategy]['average_cells_quality'])

            i += 1

        workbook.close()

    # отрисовка
    if const_draw_graphs_switch:
        # energy part
        fig1, (ax11, ax12, ax13) = plt.subplots(3, 1)
        ax11.set_title('Total energy')
        for strategy in strategies:
            ax11.plot(range(const_experiment_length), logs[strategy]['population_energy'], label=strategy)
        ax11.legend()
        ax12.set_title('Average energy')
        for strategy in strategies:
            ax12.plot(range(const_experiment_length), logs[strategy]['population_average_energy'], label=strategy)
        ax12.legend()
        ax13.set_title('Distribution of final energy')
        ax13.hist([logs[strategy]['final_energy'] for strategy in strategies],label=strategies)
        ax13.legend()
        plt.tight_layout()

        # abundance part
        fig2 = plt.figure()
        ax2 = fig2.add_subplot()
        ax2.set_title('Total abundance')
        for strategy in strategies:
            ax2.plot(range(const_experiment_length), logs[strategy]['population_abundance'], label=strategy)
        ax2.legend()
        plt.tight_layout()

        #cells quality part
        fig3, (ax31, ax32, ax33) = plt.subplots(3, 1)
        ax31.set_title('Total cells quality')
        for strategy in strategies:
            ax31.plot(range(const_experiment_length), logs[strategy]['cells_quality'], label=strategy)
        ax31.legend()
        ax32.set_title('Average cell quality')
        for strategy in strategies:
            ax32.plot(range(const_experiment_length), logs[strategy]['average_cells_quality'], label=strategy)
        ax32.plot(range(const_experiment_length), logs['weather'], label='average weather', color=(0.5, 0.5, 0.5), linestyle='--')
        ax32.legend()
        ax33.set_title('Distribution of final cells quality')
        ax33.hist([logs[strategy]['final_cells_quality'] for strategy in strategies],label=strategies)
        ax33.legend()
        plt.tight_layout()


        # energy * quality part
        fig4, (ax41, ax42, ax43) = plt.subplots(3, 1)
        ax41.set_title('Total energy * quality')
        for strategy in strategies:
            ax41.plot(range(const_experiment_length), logs[strategy]['population_energy_and_quality'], label=strategy)
        ax41.legend()
        ax42.set_title('Average energy * quality')
        for strategy in strategies:
            ax42.plot(range(const_experiment_length), logs[strategy]['average_energy_and_quality'], label=strategy)
        ax42.legend()
        ax43.set_title('Distribution of final energy * quality')
        ax43.hist([logs[strategy]['final_energy_and_quality'] for strategy in strategies],label=strategies)
        ax43.legend()
        plt.tight_layout()

        # dispersal part
        fig5, (ax51, ax52, ax53) = plt.subplots(3, 1)
        ax51.set_title('Total dispersal')
        for strategy in strategies:
            ax51.plot(range(const_experiment_length), logs[strategy]['population_dispersal'], label=strategy)
        ax51.legend()
        ax52.set_title('Average dispersal')
        for strategy in strategies:
            ax52.plot(range(const_experiment_length), logs[strategy]['population_average_dispersal'], label=strategy)
        ax52.legend()
        ax53.set_title('Distribution of final dispersal')
        ax53.hist([logs[strategy]['final_dispersal'] for strategy in strategies],label=strategies)
        ax53.legend()

        plt.tight_layout()
        plt.show()


# изменяем качество (питательность) клеток карты: сначала ухудшем, потом улучшаем
# линейно с одинаковым шагом для всех клеток
def change_map_quality_multiplicative(map, iteration, winter_hardness=const_winter_hardness):


    # для графика погоды
    q=50
    logs['weather'][iteration] = ((q - q/winter_hardness)/2) * \
                                      math.cos(2*math.pi * iteration/const_experiment_length) + \
                                      (q + q/winter_hardness)/2

    # изменяем карту
    for i in range(const_map_size):
        for j in range(const_map_size):

            q = map.cells_initial[i][j].quality

            map.cells[i][j].quality = ((q - q/winter_hardness)/2) * \
                                      math.cos(2*math.pi * iteration/const_experiment_length) + \
                                      (q + q/winter_hardness)/2


# изменяем качество (питательность) клеток карты: сначала ухудшем, потом улучшаем
# ЭТО УСТАРЕВШАЯ ФУНКЦИЯ, ЕЕ НАДО ПЕРЕПИСЫВАТЬ
def change_map_quality_additive(map, iteration, winter_hardness):

    # # шаг до середины "года" отрицательный (погода портится), после положительный (погода улучшается)
    # if iteration <= const_experiment_length/2:
    #     step = -const_normal_init_cell_energy / (const_experiment_length / 2)
    # else:
    #     step = const_normal_init_cell_energy / (const_experiment_length / 2)

    logs['weather'][iteration] = (const_normal_init_cell_energy/2) * math.cos(2 * math.pi * iteration / const_experiment_length)+25

    # шаг варьируется по синусоиде так, что нулевая клетка становится в самом плохом состоянии -50, а стандартная -- 0
    step = (const_normal_init_cell_energy/2) * (math.cos(2 * math.pi * iteration / const_experiment_length) - math.cos(
        2 * math.pi * (iteration - 1) / const_experiment_length))

    # изменяем карту
    for i in range(const_map_size):
        for j in range(const_map_size):
            map.cells[i][j].quality += step
            #if map.cells[i][j].quality<-48: print(map.cells[i][j].quality)


# создаем хэш для логирования -- вынесен в функцию просто, чтобы текст не загромождал
def declare_logs():

    #global logs
    logs = {}

    for strategy in strategies:

        # готовим хэш массивов для логирования
        logs[strategy] = {}
        logs[strategy]['population_energy'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['population_average_energy'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['final_energy'] = []
        logs[strategy]['population_abundance'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['cells_quality'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['final_cells_quality'] = []
        logs[strategy]['average_cells_quality'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['population_energy_and_quality'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['average_energy_and_quality'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['final_energy_and_quality'] = []
        logs[strategy]['population_dispersal'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['population_average_dispersal'] = [0 for i in range(const_experiment_length)]
        logs[strategy]['final_dispersal'] = []
        logs['weather'] = [0 for i in range(const_experiment_length)]

    return logs

###########################################################
#
# MAIN
#
###########################################################

background_surface = None
moving_surface = None

# общие вещи pygame
if const_draw_map_switch:
    pygame.init()
    pygame.font.init()
    myfont = pygame.font.SysFont('arial', 14)
    #print(pygame.font.get_fonts())
    #exit()
    clock = pygame.time.Clock()

    # создаем экран
    display = pygame.display.set_mode((const_screen_size, const_screen_size))
    pygame.display.set_caption('KabANimats')

    # создаем слой для отображения фона карты
    background_surface = pygame.Surface((const_screen_size, const_screen_size))

    # создаем слой для отображения движущихся кабанчиков
    moving_surface = pygame.Surface((const_screen_size, const_screen_size))


# самые глобальные логи верхнего уровня
global_logs = {}

# повторяем эксперимент для статистики
for repetition in range(const_num_of_repetitions):

    global_logs[repetition] = {}

    # различные суровости зим
    for winter_hardness in winters:

        global_logs[repetition][winter_hardness] = {}

        # различные пропорции карт
        for map_proportions in maps:

            global_logs[repetition][winter_hardness][map_proportions] = {}

            # создаем объект -- карту с заданными пропорциями
            m = map(bad_normal_good=map_proportions, brush_num=5, surface=background_surface)

            # хэш массивов для логирования
            logs = declare_logs()

            for strategy in strategies:

                print('Repetition:',repetition,
                      'Winter hardness:', winter_hardness,
                      'Map type:', map_proportions,
                      'Strategy:',strategy)


                # создаем стадо кабанов, привязанных к карте m
                kabans = [randomly_moving_kaban(surface=moving_surface, map = m,
                                                map_position=[random.randint(1,const_map_size-1),random.randint(1,const_map_size-1)],
                                                color=(0,0,0)) for i in range(const_num_of_animats)]



                ########################
                # ГЛАВНЫЙ ЖИЗНЕННЫЙ ЦИКЛ
                ########################
                for iteration in range(const_experiment_length):

                    # подставим фон
                    if const_draw_map_switch:
                        moving_surface.blit(background_surface, (0,0))

                    # жизнь кабанов
                    for kab in kabans:

                        # учитываем только еще живых
                        if kab.alive:

                            # сдвигаем кабана согласно выбранной стратегии
                            kab.live_one_day(strategy)

                            # убиваем, если энергии нет
                            if kab.energy<0: kab.alive = False

                            # пишем логи
                            logs[strategy]['population_energy'][iteration] += kab.energy
                            logs[strategy]['population_abundance'][iteration] += 1
                            logs[strategy]['cells_quality'][iteration] += m.cells[kab.pos[0]][kab.pos[1]].quality
                            logs[strategy]['population_energy_and_quality'][iteration] += kab.energy * m.cells[kab.pos[0]][kab.pos[1]].quality
                            logs[strategy]['population_dispersal'][iteration] += math.sqrt((kab.init_pos[0] - kab.pos[0])**2 + \
                                                                                         (kab.init_pos[1] - kab.pos[1])**2)



                    # меняем температуру на карте
                    #change_map_quality_additive(m, iteration)
                    change_map_quality_multiplicative(m, iteration, winter_hardness)


                    # если рисуем
                    if const_draw_map_switch:

                        # отрисовываем конечный результат движения на экран
                        display.blit(moving_surface,(0,0))

                        # служебное для pygame
                        for i in pygame.event.get():
                            if i.type == pygame.QUIT:
                                exit()

                        # отображение прогресса на экране
                        textsurface = myfont.render(' '+str(strategy)+': '+str(int(100*iteration/const_experiment_length))+'% ',
                                                    True, (0, 0, 0), (200,200,200))
                        display.blit(textsurface, (5, 0))

                        # перерисовываем экран
                        pygame.display.update()

                        # таймер, регулирующий скорость движения
                        clock.tick(const_experiment_speed)



                # рассчитываем конечные распределения
                for kab in kabans:
                    # учитываем только еще живых
                    if kab.alive:
                        logs[strategy]['final_cells_quality'].append(m.cells[kab.pos[0]][kab.pos[1]].quality)
                        logs[strategy]['final_dispersal'].append(math.sqrt((kab.init_pos[0] - kab.pos[0])**2 + \
                                                                                         (kab.init_pos[1] - kab.pos[1])**2))
                        logs[strategy]['final_energy'].append(kab.energy)
                        logs[strategy]['final_energy_and_quality'].append(kab.energy * m.cells[kab.pos[0]][kab.pos[1]].quality)


            # отрисовываем графики и создаем эксели
            write_xlsx_draw_graphs(logs)

            # записываем полученный кусок логов в общий массив
            global_logs[repetition][winter_hardness][map_proportions] = logs



# вывод файла глобальной статистики
with open('eggs.csv', 'w', newline='') as csvfile:

    csvwriter = csv.writer(csvfile, delimiter=',')
    csvwriter.writerow(['Strategy',
                        'Winter hardness',
                        'Map type',
                        'E survival rate',
                        'SD of survival rate',
                        'E total disperal',
                        'SD of total dispersal',
                        'E of average disperal',
                        'SD of average dispersal',
                        'E total energy',
                        'SD of total energy',
                        'E of average energy',
                        'SD of average energy',
                        'E total cell quality',
                        'SD of total cell quality',
                        'E of average cell quality',
                        'SD of average cell quality',
                        'E total energy*cell quality',
                        'SD of total energy*cell quality',
                        'E of average energy*cell quality',
                        'SD of average energy*cell quality'
                        ])

    # обрабатываем конечную статистику
    #for iteration in range(const_experiment_length):
    for map_proportions in maps:
        for winter_hardness in winters:
            for strategy in strategies:

                proportion_survived = []
                average_dispersal = []
                total_dispersal = []
                average_energy = []
                total_energy = []
                average_cell = []
                total_cell = []
                average_energy_and_cell = []
                total_energy_and_cell = []


                for repetition in range(const_num_of_repetitions):

                    abund = global_logs[repetition]\
                                       [winter_hardness]\
                                       [map_proportions]\
                                       [strategy]\
                                       ['population_abundance']\
                                       [const_experiment_length-1]

                    dispers = global_logs[repetition]\
                                       [winter_hardness]\
                                       [map_proportions]\
                                       [strategy]\
                                       ['population_dispersal']\
                                       [const_experiment_length-1]

                    energy = global_logs[repetition]\
                                       [winter_hardness]\
                                       [map_proportions]\
                                       [strategy]\
                                       ['population_energy']\
                                       [const_experiment_length-1]

                    cells = global_logs[repetition]\
                                       [winter_hardness]\
                                       [map_proportions]\
                                       [strategy]\
                                       ['cells_quality']\
                                       [const_experiment_length-1]

                    cells_and_quality = global_logs[repetition]\
                                       [winter_hardness]\
                                       [map_proportions]\
                                       [strategy]\
                                       ['population_energy_and_quality']\
                                       [const_experiment_length-1]



                    # abundance
                    proportion_survived.append(abund/const_num_of_animats)

                    # total dispersal
                    total_dispersal.append(dispers)

                    # average dispersal
                    if abund>0: average_dispersal.append(dispers/abund)
                    else: average_dispersal.append(0)

                    # total energy
                    total_energy.append(energy)

                    # average energy
                    if abund>0: average_energy.append(energy/abund)
                    else: average_energy.append(0)

                    # total cells quality
                    total_cell.append(cells)

                    # average cells quality
                    if abund>0: average_cell.append(cells/abund)
                    else: average_cell.append(0)

                    # total cells * energy
                    total_energy_and_cell.append(cells_and_quality)

                    # average cells * energy
                    if abund>0: average_energy_and_cell.append(cells_and_quality/abund)
                    else: average_energy_and_cell.append(0)


                csvwriter.writerow([strategy,
                                    str(winter_hardness),
                                    '('+str(map_proportions[0])+','+str(map_proportions[1])+','+str(map_proportions[2])+')',
                                    str(np.around(np.mean(proportion_survived),3)),
                                    str(np.around(np.std(proportion_survived),5)),
                                    str(np.around(np.mean(total_dispersal),3)),
                                    str(np.around(np.std(total_dispersal),5)),
                                    str(np.around(np.mean(average_dispersal),3)),
                                    str(np.around(np.std(average_dispersal),5)),
                                    str(np.around(np.mean(total_energy),3)),
                                    str(np.around(np.std(total_energy),5)),
                                    str(np.around(np.mean(average_energy),3)),
                                    str(np.around(np.std(average_energy),5)),
                                    str(np.around(np.mean(total_cell),3)),
                                    str(np.around(np.std(total_cell),5)),
                                    str(np.around(np.mean(average_cell),3)),
                                    str(np.around(np.std(average_cell),5)),
                                    str(np.around(np.mean(total_energy_and_cell),3)),
                                    str(np.around(np.std(total_energy_and_cell),5)),
                                    str(np.around(np.mean(average_energy_and_cell),3)),
                                    str(np.around(np.std(average_energy_and_cell),5))
                                    ])
