class InvertibleMap:
    def __init__(self):
        self.dic = dict()  # type : K -> {V} where K and V are frozensets
        self.inv_dic = dict()  # type : V -> {K} where K and V are frozensets

    def __getitem__(self, item):
        return self.dic[item]

    def set(self, dic, inv_dic):
        self.dic = dic
        self.inv_dic = inv_dic

    def copy(self):
        copied = InvertibleMap()
        copied.set(self.dic.copy(), self.inv_dic.copy())
        return copied

    def put(self, key, values):
        if key in self.dic.keys():
            self.dic[key] = (self.dic[key]) | (values)
        else:
            self.dic[key] = values
        for v in values:
            v_as_key = frozenset(v)
            if v_as_key in self.inv_dic.keys():
                self.inv_dic[v_as_key].add(key)
            else:
                self.inv_dic[v_as_key] = {key}

    def put_incremental_single(self, key, value):
        if key in self.dic.keys():
            self.dic[key] = frozenset(self.dic[key] | {value})
        else:
            self.dic[key] = {value}
        v_as_key = frozenset(value)
        if v_as_key in self.inv_dic.keys():
            self.inv_dic[v_as_key].add(key)
        else:
            self.inv_dic[v_as_key] = {key}

    def put_incremental_multiple(self, key, values):
        if key in self.dic.keys():
            self.dic[key] = frozenset(self.dic[key] | set(values))
        else:
            self.dic[key] = values
        for value in values:
            v_as_key = frozenset(value)
            if v_as_key in self.inv_dic.keys():
                self.inv_dic[v_as_key].add(key)
            else:
                self.inv_dic[v_as_key] = {key}

    def get_value(self, key):
        return self.dic[key]

    def get_keys_from_value(self, value):
        return self.inv_dic[value]

    def remove_value_from_keys(self, value):
        if value not in self.inv_dic.keys():
            print()
        relevant_keys = self.inv_dic[value]
        for key in relevant_keys:
            self.dic[key] = frozenset(self.dic[key] - {value})
            if len(self.dic[key]) == 0:
                del self.dic[key]
        del self.inv_dic[value]

    def remove_all_values_from_keys(self, values):
        for v in values:
            self.remove_value_from_keys(v)

    def keep_only_values(self, values):
        relevant_keys = set()
        to_remove = set()
        for v in self.inv_dic.keys():
            if v not in values:
                to_remove.add(v)
            else:
                relevant_keys.update(self.inv_dic[v])
        for v in to_remove:
            del self.inv_dic[v]

        to_remove = set()
        for key in self.dic.keys():
            if key not in relevant_keys:
                to_remove.add(key)
            else:
                new = self.dic[key].intersection(values)
                self.dic[key] = new
        for key in to_remove:
            del self.dic[key]

    def items(self):
        return self.dic.items()

    def items_inverted(self):
        return self.inv_dic.items()

    def keys(self):
        return self.dic.keys()

    def values(self):
        return self.values_single()

    def values_single(self):
        return self.inv_dic.keys()

    def __len__(self):
        return len(self.dic)
