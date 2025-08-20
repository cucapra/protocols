
# merge k sorted linked lists and return it as one sorted list.
import heapq
def mergeKLists(lists):
    # pointers = [0] * len(lists)
    min_heap = []
    res = []
    for i in range(len(lists)):
        heapq.heappush(min_heap, (lists[i][0], i, 0))
    
    while min_heap:
        val, list_idx, idx = heapq.heappop(min_heap)
        res.append(val)
        if idx < len(lists[list_idx]) - 1:
            heapq.heappush(lists[list_idx][idx + 1], list_idx, idx + 1)

    return res

print('f')
# print(mergeKLists(lists = [[1,4,5],[1,3,4],[2,6]]))


        