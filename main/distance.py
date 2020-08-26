from main import definitions, values, emitter


def calculate_distance(loc_a, loc_b):
    min_distance = 10000
    count = -1
    for loc in values.LIST_TRACE:
        if count >= 0:
            count = count + 1
            if loc == loc_b:
                if count < min_distance:
                    min_distance = count
                count = -1
        elif loc == loc_a:
            count = 0
    return min_distance


def generate_distance_map():
    loc_bug = values.CONF_BUG_LOCATION
    distance_map = dict()
    for loc in set(values.LIST_TRACE):
        if loc == loc_bug:
            continue
        distance = calculate_distance(loc, loc_bug)
        if distance > 0:
            distance_map[loc] = distance

    return distance_map


def update_distance_map():
    emitter.normal("\tupdating distance matrix")
    latest_dist_map = generate_distance_map()
    for loc in latest_dist_map:
        if loc in values.MAP_LOC_DISTANCE:
            if values.MAP_LOC_DISTANCE[loc] > latest_dist_map[loc]:
                values.MAP_LOC_DISTANCE[loc] = latest_dist_map[loc]
        else:
            values.MAP_LOC_DISTANCE[loc] = latest_dist_map[loc]

    values.MAP_LOC_DISTANCE = {k: v for k, v in sorted(values.MAP_LOC_DISTANCE.items(), key=lambda item: item[1])}
